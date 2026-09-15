import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel19
open Hf4Quad.Dag

def p0 : Cubic := ⟨(79/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((79/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((79/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((79/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((79/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(173047619047619/50000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((79/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-173047619047619/50000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((79/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-254666666666667/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((79/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((79/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(6241/1600),(79/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((79/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(94440529100529/20000000000000),(11954497354497/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((79/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-94440529100529/20000000000000),(-11954497354497/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((79/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-22714666005291/3125000000000),(-16335449735449/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((79/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((79/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(493039/64000),(18723/64000),(237/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((79/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(938179318214699/12500000000000),(285016501736111/100000000000000),(901950954861/25000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((79/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-938179318214699/12500000000000),(-285016501736111/100000000000000),(-901950954861/25000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((79/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1029037982235863/12500000000000),(-7533798786789/2500000000000),(-736693039021/20000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((79/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((79/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(38950081/2560000),(493039/640000),(18723/1280000),(79/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((79/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(2125252435515873/50000000000000),(6725482390873/3125000000000),(4086369047619/100000000000000),(4310515873/12500000000000)⟩
def e19 : ℝ := (21825397/20000000000000)
theorem h19 : Model (fun x => f19 ((79/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1990899493427579/50000000000000),(-10767064370453/12500000000000),(201451926257/50000000000000),(19261326059/100000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((79/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((79/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(3004937889648437/100000000000000),(47546485595703/25000000000000),(493039/10240000),(6241/10240000)⟩
def e22 : ℝ := (386718751/100000000000000)
theorem h22 : Model (fun x => f22 ((79/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(9788306940540001/50000000000000),(61951309750253/5000000000000),(784193794307/2500000000000),(49632518627/12500000000000)⟩
def e23 : ℝ := (50388021/2000000000000)
theorem h23 : Model (fun x => f23 ((79/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(3898703723556211/25000000000000),(288222420010359/25000000000000),(15885327812397/50000000000000),(16652859003/4000000000000)⟩
def e24 : ℝ := (1314264021/50000000000000)
theorem h24 : Model (fun x => f24 ((79/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((79/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(5934752332055663/100000000000000),(14085646357727/3125000000000),(1426394567871/10000000000000),(120370849609/50000000000000)⟩
def e26 : ℝ := (459423829/20000000000000)
theorem h26 : Model (fun x => f26 ((79/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(6663251031016993/50000000000000),(1012139397116501/100000000000000),(32029727756849/100000000000000),(135146530619/25000000000000)⟩
def e27 : ℝ := (64477339/1250000000000)
theorem h27 : Model (fun x => f27 ((79/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(2892131695625883/10000000000000),(2165029077157937/100000000000000),(63800383381643/100000000000000),(956907597551/100000000000000)⟩
def e28 : ℝ := (3893357581/50000000000000)
theorem h28 : Model (fun x => f28 ((79/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((79/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(5860567927904967/50000000000000),(1038581658109737/100000000000000),(39439809801633/100000000000000),(832063497923/100000000000000)⟩
def e30 : ℝ := (10612780773/100000000000000)
theorem h30 : Model (fun x => f30 ((79/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(1390722071780623/50000000000000),(49291415202351/20000000000000),(2924727959/31250000000),(24681248599/12500000000000)⟩
def e31 : ℝ := (100737189/4000000000000)
theorem h31 : Model (fun x => f31 ((79/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(7925690274955019/25000000000000),(602871538292423/25000000000000),(73159512850443/100000000000000),(1154357586343/100000000000000)⟩
def e32 : ℝ := (10305144887/100000000000000)
theorem h32 : Model (fun x => f32 ((79/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((79/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(2677389/320),(33891/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((79/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((79/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(174511/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((79/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1093913/64),(51563/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((79/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((79/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1239833/64),(51563/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((79/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1239833/64),(-51563/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((79/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((79/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(119/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((79/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(14161/1600),(119/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((79/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((79/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(297381/160),(2499/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((79/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(26901516909/50000000000000),(-90425267/10000000000000),(5699071/50000000000000),(-127711/100000000000000)⟩
def e46 : ℝ := (1377/100000000000000)
theorem h46 : Model (fun x => f46 ((79/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (146181/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-521146693966191/50000000000000),(44624873051/25000000000000),(-1526573791/100000000000000),(653307/5000000000000)⟩
def e47 : ℝ := (53169237/100000000000000)
theorem h47 : Model (fun x => f47 ((79/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((79/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(159/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((79/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((79/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((79/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(66249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((79/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(116249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((79/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((79/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(116249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((79/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((79/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2441249999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((79/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((79/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(16249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((79/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(99175781249993/25000000000000),(11593749999981/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (17/20000000000000)
theorem h60 : Model (fun x => f60 ((79/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(135140624999997/100000000000000),(484374999999/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (9/100000000000000)
theorem h61 : Model (fun x => f61 ((79/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((79/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(116249999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((79/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1297640624999987/100000000000000),(2567708333329/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (39/100000000000000)
theorem h64 : Model (fun x => f64 ((79/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1397640624999987/100000000000000),(2567708333329/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (39/100000000000000)
theorem h65 : Model (fun x => f65 ((79/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(693060504455511/12500000000000),(5700353698721/3125000000000),(27795776367/2500000000000),(518391927/25000000000000)⟩
def e66 : ℝ := (63431/10000000000000)
theorem h66 : Model (fun x => f66 ((79/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(216249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((79/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(93528124999999/20000000000000),(180208333333/10000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (3/20000000000000)
theorem h68 : Model (fun x => f68 ((79/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(252818212890621/25000000000000),(5845507812489/100000000000000),(11263020833/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (49/100000000000000)
theorem h69 : Model (fun x => f69 ((79/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(2803493090584233/5000000000000),(67774355881509/3125000000000),(1126549493439/5000000000000),(21381539981/20000000000000)⟩
def e70 : ℝ := (266400277/100000000000000)
theorem h70 : Model (fun x => f70 ((79/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((79/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2837953124999937/12500000000000),(10171874999979/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (189/12500000000000)
theorem h72 : Model (fun x => f72 ((79/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(3689339062499691/100000000000000),(12104531249979/10000000000000),(725520833327/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (47/5000000000000)
theorem h73 : Model (fun x => f73 ((79/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(18654642170574619/50000000000000),(719879493263487/50000000000000),(7414119722951/50000000000000),(535940541/781250000000)⟩
def e74 : ℝ := (16171177/10000000000000)
theorem h74 : Model (fun x => f74 ((79/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(46689573076416949/50000000000000),(1804269187367631/50000000000000),(18679614657341/50000000000000),(175508089153/100000000000000)⟩
def e75 : ℝ := (428112047/100000000000000)
theorem h75 : Model (fun x => f75 ((79/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((79/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(945984374999979/12500000000000),(3390624999993/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (63/12500000000000)
theorem h77 : Model (fun x => f77 ((79/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(2640624999999/100000000000000),(67708333333/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((79/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(429101562499/100000000000000),(33007812499/100000000000000),(423177083/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((79/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(3247386987297/10000000000000),(2730777587813/100000000000000),(16474989139/20000000000000),(519341351/50000000000000)⟩
def e80 : ℝ := (2377261/50000000000000)
theorem h80 : Model (fun x => f80 ((79/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(70224743600297/100000000000000),(3020307162391/50000000000000),(94757030007/50000000000000),(2589380283/100000000000000)⟩
def e81 : ℝ := (14629313/100000000000000)
theorem h81 : Model (fun x => f81 ((79/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(18689874179286839/20000000000000),(903644747265011/25000000000000),(4693592921837/12500000000000),(44524367359/25000000000000)⟩
def e82 : ℝ := (5534267/1250000000000)
theorem h82 : Model (fun x => f82 ((79/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(34864501953/50000000000000),(1787923177/25000000000000),(17191569/6250000000000),(4701967/100000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((79/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(5665481567/50000000000000),(1452687581/100000000000000),(74496799/100000000000000),(955087/50000000000000)⟩
def e84 : ℝ := (24617/100000000000000)
theorem h84 : Model (fun x => f84 ((79/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(1841281509/100000000000000),(141637039/50000000000000),(9079297/50000000000000),(310403/50000000000000)⟩
def e85 : ℝ := (377/3125000000000)
theorem h85 : Model (fun x => f85 ((79/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(59841649/20000000000000),(53704043/100000000000000),(103277/2500000000000),(176541/100000000000000)⟩
def e86 : ℝ := (23/500000000000)
theorem h86 : Model (fun x => f86 ((79/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(179524947/20000000000000),(161112129/100000000000000),(309831/2500000000000),(529623/100000000000000)⟩
def e87 : ℝ := (69/500000000000)
theorem h87 : Model (fun x => f87 ((79/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-179524947/20000000000000),(-161112129/100000000000000),(-309831/2500000000000),(-529623/100000000000000)⟩
def e88 : ℝ := (69/500000000000)
theorem h88 : Model (fun x => f88 ((79/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(4672468499940473/5000000000000),(722915765589583/20000000000000),(2346795686341/6250000000000),(178096939813/100000000000000)⟩
def e89 : ℝ := (11068879/2500000000000)
theorem h89 : Model (fun x => f89 ((79/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2837953124999937/10000000000000),(10171874999979/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (189/10000000000000)
theorem h90 : Model (fun x => f90 ((79/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2186877541503861/100000000000000),(16854547526011/100000000000000),(48712565103/100000000000000),(62572337/100000000000000)⟩
def e91 : ℝ := (30279/100000000000000)
theorem h91 : Model (fun x => f91 ((79/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(24825023811612247/4000000000000),(9232170580678019/100000000000000),(28042929397731/50000000000000),(44576557937/25000000000000)⟩
def e92 : ℝ := (156909011/50000000000000)
theorem h92 : Model (fun x => f92 ((79/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(16112774071/100000000000000),(-239686987/100000000000000),(27/1280000000),(-14347/100000000000000)⟩
def e93 : ℝ := (13/12500000000000)
theorem h93 : Model (fun x => f93 ((79/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (152834290057695731/25000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(15057285858681/100000000000000),(89605735211/25000000000000),(-40145953/6250000000000),(191847/12500000000000)⟩
def e94 : ℝ := (32847/10000000000000)
theorem h94 : Model (fun x => f94 ((79/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(66249999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((79/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(10752688172043/25000000000000),(-154160403901/100000000000000),(442037/80000000000),(-1980453/100000000000000)⟩
def e96 : ℝ := (891/12500000000000)
theorem h96 : Model (fun x => f96 ((79/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (11583333333333/5000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(56989247311827/50000000000000),(154160403899/50000000000000),(-1105092503/100000000000000),(3960903/100000000000000)⟩
def e97 : ℝ := (26011/50000000000000)
theorem h97 : Model (fun x => f97 ((79/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1196774193548367/50000000000000),(3237368481879/50000000000000),(-23206942563/100000000000000),(83178963/100000000000000)⟩
def e98 : ℝ := (546231/50000000000000)
theorem h98 : Model (fun x => f98 ((79/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(6989247311827/50000000000000),(154160403899/50000000000000),(-1105092503/100000000000000),(3960903/100000000000000)⟩
def e99 : ℝ := (26011/50000000000000)
theorem h99 : Model (fun x => f99 ((79/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(334582032604873/100000000000000),(8284878480507/100000000000000),(-9731943691/100000000000000),(-36670369/100000000000000)⟩
def e100 : ℝ := (2175861/100000000000000)
theorem h100 : Model (fun x => f100 ((79/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(129910972366743/100000000000000),(702838830679/100000000000000),(-784259197/50000000000000),(1107347/50000000000000)⟩
def e101 : ℝ := (155637/100000000000000)
theorem h101 : Model (fun x => f101 ((79/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(56989247311827/5000000000000),(154160403899/5000000000000),(-1105092503/10000000000000),(3960903/10000000000000)⟩
def e102 : ℝ := (26011/5000000000000)
theorem h102 : Model (fun x => f102 ((79/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1269695918603283/100000000000000),(3786046908659/100000000000000),(-394357607/3125000000000),(10455931/25000000000000)⟩
def e103 : ℝ := (675857/100000000000000)
theorem h103 : Model (fun x => f103 ((79/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1369695918603283/100000000000000),(3786046908659/100000000000000),(-394357607/3125000000000),(10455931/25000000000000)⟩
def e104 : ℝ := (675857/100000000000000)
theorem h104 : Model (fun x => f104 ((79/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(4582756444968851/100000000000000),(126145075111111/100000000000000),(138148959749/100000000000000),(-444074847/25000000000000)⟩
def e105 : ℝ := (35508069/100000000000000)
theorem h105 : Model (fun x => f105 ((79/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(106989247311827/50000000000000),(154160403899/50000000000000),(-1105092503/100000000000000),(3960903/100000000000000)⟩
def e106 : ℝ := (26011/50000000000000)
theorem h106 : Model (fun x => f106 ((79/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(457867961614051/100000000000000),(52779217851/4000000000000),(-18893517/500000000000),(20273/200000000000)⟩
def e107 : ℝ := (259681/100000000000000)
theorem h107 : Model (fun x => f107 ((79/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(244934742906439/25000000000000),(4235106593689/100000000000000),(-9077244399/100000000000000),(13593627/100000000000000)⟩
def e108 : ℝ := (230221/25000000000000)
theorem h108 : Model (fun x => f108 ((79/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(359192406928407/800000000000),(1429977082023719/100000000000000),(4906163741/78125000000),(-11189937801/50000000000000)⟩
def e109 : ℝ := (92711819/20000000000000)
theorem h109 : Model (fun x => f109 ((79/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2728130419701603/12500000000000),(14759615444259/12500000000000),(-16469443137/6250000000000),(23254287/6250000000000)⟩
def e110 : ℝ := (3268377/12500000000000)
theorem h110 : Model (fun x => f110 ((79/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(3050812512354063/100000000000000),(83796526393237/100000000000000),(21508480757/25000000000000),(-1200840367/100000000000000)⟩
def e111 : ℝ := (23901937/100000000000000)
theorem h111 : Model (fun x => f111 ((79/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(29889999134767587/100000000000000),(950192387815001/100000000000000),(514356297423/12500000000000),(-15313172141/100000000000000)⟩
def e112 : ℝ := (311454209/100000000000000)
theorem h112 : Model (fun x => f112 ((79/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(37394525000409231/50000000000000),(3719014796623/156250000000),(1299342495983/12500000000000),(-37693047743/100000000000000)⟩
def e113 : ℝ := (96876663/12500000000000)
theorem h113 : Model (fun x => f113 ((79/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(909376806567201/12500000000000),(4919871814753/12500000000000),(-5489814379/6250000000000),(7751429/6250000000000)⟩
def e114 : ℝ := (1089459/12500000000000)
theorem h114 : Model (fun x => f114 ((79/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(390796623887/20000000000000),(86197215083/100000000000000),(160416653/25000000000000),(-713389/12500000000000)⟩
def e115 : ℝ := (51593/100000000000000)
theorem h115 : Model (fun x => f115 ((79/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(273137425297/100000000000000),(9036804807/50000000000000),(333865961/100000000000000),(305459/100000000000000)⟩
def e116 : ℝ := (14899/50000000000000)
theorem h116 : Model (fun x => f116 ((79/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(3974157433129/20000000000000),(284472360227/20000000000000),(15581234257/50000000000000),(27618367/20000000000000)⟩
def e117 : ℝ := (117787/5000000000000)
theorem h117 : Model (fun x => f117 ((79/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(42519211246917/100000000000000),(124192565667/4000000000000),(70846827829/100000000000000),(376635853/100000000000000)⟩
def e118 : ℝ := (519719/10000000000000)
theorem h118 : Model (fun x => f118 ((79/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(74831569212065379/100000000000000),(476654856796079/20000000000000),(10465586795693/100000000000000),(-3731641189/10000000000000)⟩
def e119 : ℝ := (390105247/50000000000000)
theorem h119 : Model (fun x => f119 ((79/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(3818050031/10000000000000),(210534879/6250000000000),(99375713/100000000000000),(176633/20000000000000)⟩
def e120 : ℝ := (6453/100000000000000)
theorem h120 : Model (fun x => f120 ((79/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(5337059183/100000000000000),(294296067/50000000000000),(745477/3125000000000),(78827/20000000000000)⟩
def e121 : ℝ := (271/10000000000000)
theorem h121 : Model (fun x => f121 ((79/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(74604053/10000000000000),(98731583/100000000000000),(5090379/100000000000000),(122351/100000000000000)⟩
def e122 : ℝ := (343/25000000000000)
theorem h122 : Model (fun x => f122 ((79/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(20857047/20000000000000),(16101387/100000000000000),(1007723/100000000000000),(3967/12500000000000)⟩
def e123 : ℝ := (21/4000000000000)
theorem h123 : Model (fun x => f123 ((79/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(62571141/20000000000000),(48304161/100000000000000),(3023169/100000000000000),(11901/12500000000000)⟩
def e124 : ℝ := (63/4000000000000)
theorem h124 : Model (fun x => f124 ((79/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-62571141/20000000000000),(-48304161/100000000000000),(-3023169/100000000000000),(-11901/12500000000000)⟩
def e125 : ℝ := (63/4000000000000)
theorem h125 : Model (fun x => f125 ((79/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(37415784449604837/50000000000000),(1191637117838117/50000000000000),(2616395943131/25000000000000),(-18658253549/50000000000000)⟩
def e126 : ℝ := (780212069/100000000000000)
theorem h126 : Model (fun x => f126 ((79/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2728130419701603/10000000000000),(14759615444259/10000000000000),(-16469443137/5000000000000),(23254287/5000000000000)⟩
def e127 : ℝ := (3268377/10000000000000)
theorem h127 : Model (fun x => f127 ((79/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2096430702726061/100000000000000),(12082956446511/100000000000000),(-8596328991/50000000000000),(-689493/10000000000000)⟩
def e128 : ℝ := (559143/20000000000000)
theorem h128 : Model (fun x => f128 ((79/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(57193363729033753/10000000000000),(399414950121441/6250000000000),(6238188484559/100000000000000),(-57306441433/100000000000000)⟩
def e129 : ℝ := (1558697921/100000000000000)
theorem h129 : Model (fun x => f129 ((79/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(17484546017/100000000000000),(-24420977/12500000000000),(996141/50000000000000),(-18379/100000000000000)⟩
def e130 : ℝ := (109/50000000000000)
theorem h130 : Model (fun x => f130 ((79/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (565536701034770561/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(523358403977/4000000000000),(270507878611/100000000000000),(-10433087/781250000000),(1351449/20000000000000)⟩
def e131 : ℝ := (465597/100000000000000)
theorem h131 : Model (fun x => f131 ((79/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(14070622979053/50000000000000),(125786163891/20000000000000),(-123610649/6250000000000),(8292021/100000000000000)⟩
def e132 : ℝ := (794067/100000000000000)
theorem h132 : Model (fun x => f132 ((79/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-36664293237891/12500000000000),(-3252536182357/50000000000000),(10653605687/50000000000000),(-5992601/6250000000000)⟩
def e133 : ℝ := (23703437/100000000000000)
theorem h133 : Model (fun x => f133 ((79/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(10126582278481/20000000000000),(-320461464509/50000000000000),(2028237117/25000000000000),(-102695551/100000000000000)⟩
def e134 : ℝ := (329153/25000000000000)
theorem h134 : Model (fun x => f134 ((79/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (39/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-18564199107793/12500000000000),(-706894314723/50000000000000),(28684520057/100000000000000),(-205821421/50000000000000)⟩
def e135 : ℝ := (25156701/100000000000000)
theorem h135 : Model (fun x => f135 ((79/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(38950081/256000),(493039/64000),(18723/128000),(79/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((79/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((79/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(4437351/32000),(168507/32000),(2133/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((79/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(74448889/256000),(830053/64000),(5451/25600),(97/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((79/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-6241/1600),(-79/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((79/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(73450329/256000),(823733/64000),(1087/5120),(97/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((79/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((79/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(237/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((79/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-237/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((79/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(70416729/256000),(814133/64000),(1087/5120),(97/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((79/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(71184729/256000),(814133/64000),(1087/5120),(97/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((79/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((79/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(71184729/4000),(814133/1000),(1087/80),(97/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((79/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((79/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(7361565309/512000),(93184371/128000),(3538647/256000),(14931/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((79/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(1391008511/20000000000000),(-176077027/50000000000000),(2228823/20000000000000),(-28213/10000000000000)⟩
def e151 : ℝ := (1793/25000000000000)
theorem h151 : Model (fun x => f151 ((79/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (3490845309/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(24754640973057/20000000000000),(-604668064631/100000000000000),(244964233/4000000000000),(-29149601/50000000000000)⟩
def e152 : ℝ := (250610439/100000000000000)
theorem h152 : Model (fun x => f152 ((79/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(199/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((79/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(31641/1600),(179/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((79/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(357/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((79/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(2801120448179/50000000000000),(-735588353/1562500000000),(197805271/50000000000000),(-3324459/100000000000000)⟩
def e156 : ℝ := (28177/100000000000000)
theorem h156 : Model (fun x => f156 ((79/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (177/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(110787815126039/100000000000000),(322511357469/100000000000000),(791221069/100000000000000),(-664893/10000000000000)⟩
def e157 : ℝ := (1062211/100000000000000)
theorem h157 : Model (fun x => f157 ((79/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(210787815126039/100000000000000),(322511357469/100000000000000),(791221069/100000000000000),(-664893/10000000000000)⟩
def e158 : ℝ := (1062211/100000000000000)
theorem h158 : Model (fun x => f158 ((79/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(105393907563019/100000000000000),(80627839367/50000000000000),(197805267/50000000000000),(-664893/20000000000000)⟩
def e159 : ℝ := (531107/100000000000000)
theorem h159 : Model (fun x => f159 ((79/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(5393907563019/100000000000000),(80627839367/50000000000000),(197805267/50000000000000),(-664893/20000000000000)⟩
def e160 : ℝ := (531107/100000000000000)
theorem h160 : Model (fun x => f160 ((79/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((79/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((79/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(38895370648257/10000000000000),(297555121473/50000000000000),(182498907/12500000000000),(-12268859/100000000000000)⟩
def e163 : ℝ := (49001/2500000000000)
theorem h163 : Model (fun x => f163 ((79/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(548933598439371/20000000000000),(297555121473/50000000000000),(182498907/12500000000000),(-12268859/100000000000000)⟩
def e164 : ℝ := (1960041/100000000000000)
theorem h164 : Model (fun x => f164 ((79/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((79/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1446356423303861/50000000000000),(126328573479/2500000000000),(3339146649/25000000000000),(-77709/78125000000)⟩
def e166 : ℝ := (8341559/50000000000000)
theorem h166 : Model (fun x => f166 ((79/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4087546899494337/50000000000000),(126328573479/2500000000000),(3339146649/25000000000000),(-77709/78125000000)⟩
def e167 : ℝ := (16683119/100000000000000)
theorem h167 : Model (fun x => f167 ((79/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((79/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8616050801696221/100000000000000),(740340311641/4000000000000),(54567040707/100000000000000),(-335081819/100000000000000)⟩
def e169 : ℝ := (15332939/25000000000000)
theorem h169 : Model (fun x => f169 ((79/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(86781865129649/625000000000),(740340311641/4000000000000),(54567040707/100000000000000),(-335081819/100000000000000)⟩
def e170 : ℝ := (61331757/100000000000000)
theorem h170 : Model (fun x => f170 ((79/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((79/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(14634047794592973/100000000000000),(41897349293821/100000000000000),(142287268313/100000000000000),(-326773501/50000000000000)⟩
def e172 : ℝ := (13952533/10000000000000)
theorem h172 : Model (fun x => f172 ((79/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(8484881040153629/50000000000000),(41897349293821/100000000000000),(142287268313/100000000000000),(-326773501/50000000000000)⟩
def e173 : ℝ := (139525331/100000000000000)
theorem h173 : Model (fun x => f173 ((79/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((79/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(17885095360583281/100000000000000),(71521958608229/100000000000000),(284658133399/100000000000000),(-857755897/100000000000000)⟩
def e175 : ℝ := (119759401/50000000000000)
theorem h175 : Model (fun x => f175 ((79/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(18287476312964233/100000000000000),(71521958608229/100000000000000),(284658133399/100000000000000),(-857755897/100000000000000)⟩
def e176 : ℝ := (239518803/100000000000000)
theorem h176 : Model (fun x => f176 ((79/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((79/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(9636942940447259/50000000000000),(104869380994607/100000000000000),(487692732479/100000000000000),(-3850037/500000000000)⟩
def e178 : ℝ := (70596103/20000000000000)
theorem h178 : Model (fun x => f178 ((79/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(1925626683327547/10000000000000),(104869380994607/100000000000000),(487692732479/100000000000000),(-3850037/500000000000)⟩
def e179 : ℝ := (88245129/25000000000000)
theorem h179 : Model (fun x => f179 ((79/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((79/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(10147466033175317/50000000000000),(70788881124097/50000000000000),(151857215963/20000000000000),(-50080439/20000000000000)⟩
def e181 : ℝ := (59779933/12500000000000)
theorem h181 : Model (fun x => f181 ((79/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(20298265399683967/100000000000000),(70788881124097/50000000000000),(151857215963/20000000000000),(-50080439/20000000000000)⟩
def e182 : ℝ := (95647893/20000000000000)
theorem h182 : Model (fun x => f182 ((79/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(547434836277611/50000000000000),(40368679266947/100000000000000),(174779723437/50000000000000),(1096173271/100000000000000)⟩
def e183 : ℝ := (137263283/100000000000000)
theorem h183 : Model (fun x => f183 ((79/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(111078757514021/100000000000000),(33990732197/10000000000000),(54696637/5000000000000),(-5731679/100000000000000)⟩
def e184 : ℝ := (282603/25000000000000)
theorem h184 : Model (fun x => f184 ((79/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(205393907563019/100000000000000),(80627839367/50000000000000),(197805267/50000000000000),(-664893/20000000000000)⟩
def e185 : ℝ := (531107/100000000000000)
theorem h185 : Model (fun x => f185 ((79/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(421866572640059/100000000000000),(331209339719/50000000000000),(117822113/6250000000000),(-12380609/100000000000000)⟩
def e186 : ℝ := (1096313/50000000000000)
theorem h186 : Model (fun x => f186 ((79/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(866488238247599/100000000000000),(2040851415187/100000000000000),(413070463/6250000000000),(-8448327/25000000000000)⟩
def e187 : ℝ := (3392899/50000000000000)
theorem h187 : Model (fun x => f187 ((79/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(355942810222141/20000000000000),(174657686217/3125000000000),(20293652587/100000000000000),(-39742039/50000000000000)⟩
def e188 : ℝ := (1865799/10000000000000)
theorem h188 : Model (fun x => f188 ((79/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1976884255276219/100000000000000),(766101323621/6250000000000),(30504194137/50000000000000),(-60177409/100000000000000)⟩
def e189 : ℝ := (41340759/100000000000000)
theorem h189 : Model (fun x => f189 ((79/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((79/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(105393907563019/12500000000000),(80627839367/6250000000000),(197805267/6250000000000),(-664893/2500000000000)⟩
def e191 : ℝ := (531107/12500000000000)
theorem h191 : Model (fun x => f191 ((79/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(954230018018173/100000000000000),(814976375921/50000000000000),(1064704253/25000000000000),(-32327399/100000000000000)⟩
def e192 : ℝ := (1344817/25000000000000)
theorem h192 : Model (fun x => f192 ((79/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1054230018018173/100000000000000),(814976375921/50000000000000),(1064704253/25000000000000),(-32327399/100000000000000)⟩
def e193 : ℝ := (1344817/25000000000000)
theorem h193 : Model (fun x => f193 ((79/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(5210226810149227/25000000000000),(4036145031809/2500000000000),(231788514841/25000000000000),(60738497/25000000000000)⟩
def e194 : ℝ := (109174873/20000000000000)
theorem h194 : Model (fun x => f194 ((79/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(479825560593/100000000000000),(-464626019/12500000000000),(7448003/100000000000000),(102069/100000000000000)⟩
def e195 : ℝ := (13859/100000000000000)
theorem h195 : Model (fun x => f195 ((79/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (20678533496436831/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(52534645441/1000000000000),(153002846613/100000000000000),(129157201/50000000000000),(-3609251/100000000000000)⟩
def e196 : ℝ := (169611/20000000000000)
theorem h196 : Model (fun x => f196 ((79/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(110787815126039/50000000000000),(322511357469/50000000000000),(791221069/50000000000000),(-664893/5000000000000)⟩
def e197 : ℝ := (1062211/50000000000000)
theorem h197 : Model (fun x => f197 ((79/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(47441072407437/100000000000000),(-58068953/80000000000),(-13403531/20000000000000),(935723/50000000000000)⟩
def e198 : ℝ := (244721/100000000000000)
theorem h198 : Model (fun x => f198 ((79/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (5261612620909/2500000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(105117855185123/100000000000000),(145172382499/100000000000000),(134035307/100000000000000),(-3742893/100000000000000)⟩
def e199 : ℝ := (1573921/100000000000000)
theorem h199 : Model (fun x => f199 ((79/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(5117855185123/100000000000000),(145172382499/100000000000000),(134035307/100000000000000),(-3742893/100000000000000)⟩
def e200 : ℝ := (1573921/100000000000000)
theorem h200 : Model (fun x => f200 ((79/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(19396747087731/5000000000000),(535755221127/100000000000000),(494654109/100000000000000),(-6906529/50000000000000)⟩
def e201 : ℝ := (145213/2500000000000)
theorem h201 : Model (fun x => f201 ((79/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(548729845493781/20000000000000),(535755221127/100000000000000),(494654109/100000000000000),(-6906529/50000000000000)⟩
def e202 : ℝ := (5808521/100000000000000)
theorem h202 : Model (fun x => f202 ((79/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2884065221718509/100000000000000),(4546195348423/100000000000000),(4975197073/100000000000000),(-115775643/100000000000000)⟩
def e203 : ℝ := (49345027/100000000000000)
theorem h203 : Model (fun x => f203 ((79/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8166446174099461/100000000000000),(4546195348423/100000000000000),(4975197073/100000000000000),(-115775643/100000000000000)⟩
def e204 : ℝ := (12336257/25000000000000)
theorem h204 : Model (fun x => f204 ((79/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8584393063060889/100000000000000),(8317143759613/50000000000000),(4555112351/20000000000000),(-25877881/6250000000000)⟩
def e205 : ℝ := (22609887/12500000000000)
theorem h205 : Model (fun x => f205 ((79/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(3463360170527127/25000000000000),(8317143759613/50000000000000),(4555112351/20000000000000),(-25877881/6250000000000)⟩
def e206 : ℝ := (180879097/100000000000000)
theorem h206 : Model (fun x => f206 ((79/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(14562439714375737/100000000000000),(37596976161839/100000000000000),(33329037637/50000000000000),(-449198097/50000000000000)⟩
def e207 : ℝ := (409898037/100000000000000)
theorem h207 : Model (fun x => f207 ((79/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8449077000045011/50000000000000),(37596976161839/100000000000000),(33329037637/50000000000000),(-449198097/50000000000000)⟩
def e208 : ℝ := (204949019/50000000000000)
theorem h208 : Model (fun x => f208 ((79/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(8881488525386849/50000000000000),(64052587716067/100000000000000),(36824864417/25000000000000),(-285938459/20000000000000)⟩
def e209 : ℝ := (700653889/100000000000000)
theorem h209 : Model (fun x => f209 ((79/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(363307160063093/2000000000000),(64052587716067/100000000000000),(36824864417/25000000000000),(-285938459/20000000000000)⟩
def e210 : ℝ := (70065389/10000000000000)
theorem h210 : Model (fun x => f210 ((79/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2386879339951907/12500000000000),(93701789400351/100000000000000),(136086345803/50000000000000),(-75323223/4000000000000)⟩
def e211 : ℝ := (514366163/50000000000000)
theorem h211 : Model (fun x => f211 ((79/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(1192338479499763/6250000000000),(93701789400351/100000000000000),(136086345803/50000000000000),(-75323223/4000000000000)⟩
def e212 : ℝ := (1028732327/100000000000000)
theorem h212 : Model (fun x => f212 ((79/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(20053770179152933/100000000000000),(31548112534501/25000000000000),(111925422149/25000000000000),(-1086394053/50000000000000)⟩
def e213 : ℝ := (1390507631/100000000000000)
theorem h213 : Model (fun x => f213 ((79/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(10028551756243133/50000000000000),(31548112534501/25000000000000),(111925422149/25000000000000),(-1086394053/50000000000000)⟩
def e214 : ℝ := (86906727/6250000000000)
theorem h214 : Model (fun x => f214 ((79/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(205298702419853/20000000000000),(8893930470497/25000000000000),(232992910751/100000000000000),(-42834427/100000000000000)⟩
def e215 : ℝ := (99539541/25000000000000)
theorem h215 : Model (fun x => f215 ((79/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(27624408696801/25000000000000),(38150523701/12500000000000),(246270143/50000000000000),(-3739867/50000000000000)⟩
def e216 : ℝ := (3324219/100000000000000)
theorem h216 : Model (fun x => f216 ((79/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(205117855185123/100000000000000),(145172382499/100000000000000),(134035307/100000000000000),(-3742893/100000000000000)⟩
def e217 : ℝ := (1573921/100000000000000)
theorem h217 : Model (fun x => f217 ((79/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(8414666903149/2000000000000),(297774477303/50000000000000),(7606109/1000000000000),(-187069/1250000000000)⟩
def e218 : ℝ := (6472061/100000000000000)
theorem h218 : Model (fun x => f218 ((79/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(431499606817791/50000000000000),(916182931699/50000000000000),(2988652601/100000000000000),(-4454211/10000000000000)⟩
def e219 : ℝ := (19959201/100000000000000)
theorem h219 : Model (fun x => f219 ((79/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1770165477273783/100000000000000),(626418259691/12500000000000),(9947072939/100000000000000),(-116870243/100000000000000)⟩
def e220 : ℝ := (27355059/50000000000000)
theorem h220 : Model (fun x => f220 ((79/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1955990984207151/100000000000000),(10940038086303/100000000000000),(4375612077/12500000000000),(-103250371/50000000000000)⟩
def e221 : ℝ := (24063121/20000000000000)
theorem h221 : Model (fun x => f221 ((79/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(105117855185123/12500000000000),(145172382499/12500000000000),(134035307/12500000000000),(-3742893/12500000000000)⟩
def e222 : ℝ := (1573921/12500000000000)
theorem h222 : Model (fun x => f222 ((79/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(237860119067047/25000000000000),(916614531/62500000000),(782411371/50000000000000),(-18711439/50000000000000)⟩
def e223 : ℝ := (15915587/100000000000000)
theorem h223 : Model (fun x => f223 ((79/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(262860119067047/25000000000000),(916614531/62500000000),(782411371/50000000000000),(-18711439/50000000000000)⟩
def e224 : ℝ := (15915587/100000000000000)
theorem h224 : Model (fun x => f224 ((79/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(10283040460055243/50000000000000),(143714224696613/100000000000000),(279554104761/50000000000000),(-2218652351/100000000000000)⟩
def e225 : ℝ := (99153681/6250000000000)
theorem h225 : Model (fun x => f225 ((79/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(97247502223/20000000000000),(-3397791111/100000000000000),(2104937/20000000000000),(71281/100000000000000)⟩
def e226 : ℝ := (49/125000000000)
theorem h226 : Model (fun x => f226 ((79/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (1276362736380819/6250000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1247799126247/25000000000000),(138104399331/100000000000000),(32145423/100000000000000),(-1824481/50000000000000)⟩
def e227 : ℝ := (2417487/100000000000000)
theorem h227 : Model (fun x => f227 ((79/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(40018207223/390625000000),(36388405743/12500000000000),(11618393/4000000000000),(-7258213/100000000000000)⟩
def e228 : ℝ := (1632771/50000000000000)
theorem h228 : Model (fun x => f228 ((79/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(12680145308041/100000000000000),(149183287103/50000000000000),(-6041619/781250000000),(1115119/100000000000000)⟩
def e229 : ℝ := (30574961/100000000000000)
theorem h229 : Model (fun x => f229 ((79/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(802540842281/12500000000000),(6980172443/10000000000000),(-51004969/4000000000000),(1670543/10000000000000)⟩
def e230 : ℝ := (8113769/50000000000000)
theorem h230 : Model (fun x => f230 ((79/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-2220207283189/1562500000000),(-167998363127/12500000000000),(3426174479/12500000000000),(-98734353/25000000000000)⟩
def e231 : ℝ := (41384239/100000000000000)
theorem h231 : Model (fun x => f231 ((79/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((79/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-6241/320),(-79/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((79/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1659/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((79/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(7031/320),(1/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((79/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((79/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15351/320),(1/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((79/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((79/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(383775/32),(125/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((79/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(12719/1600),(41/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((79/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(22319/1600),(41/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((79/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((79/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4218291/1600),(7749/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((79/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(7586010543/20000000000000),(-34838751/25000000000000),(2211441/100000000000000),(-14369/100000000000000)⟩
def e244 : ℝ := (39/25000000000000)
theorem h244 : Model (fun x => f244 ((79/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1050651/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(454893936896847/100000000000000),(-1374951671293/100000000000000),(-4199821847/100000000000000),(-46178989/100000000000000)⟩
def e245 : ℝ := (1861709/50000000000000)
theorem h245 : Model (fun x => f245 ((79/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(711/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((79/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(63121/1600),(439/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((79/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(96721/1600),(439/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((79/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(25281/1600),(159/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((79/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2445203601/2560000),(13238499/640000),(200603/1280000),(299/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((79/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((79/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(127449/160),(1071/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((79/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(125540412243/100000000000000),(-421984579/20000000000000),(13297833/50000000000000),(-297991/100000000000000)⟩
def e253 : ℝ := (3207/100000000000000)
theorem h253 : Model (fun x => f253 ((79/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (62649/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(119910885971721/100000000000000),(290756919349/50000000000000),(358450817/25000000000000),(-6511433/100000000000000)⟩
def e254 : ℝ := (3097971/50000000000000)
theorem h254 : Model (fun x => f254 ((79/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(219910885971721/100000000000000),(290756919349/50000000000000),(358450817/25000000000000),(-6511433/100000000000000)⟩
def e255 : ℝ := (3097971/50000000000000)
theorem h255 : Model (fun x => f255 ((79/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(5497772149293/5000000000000),(290756919349/100000000000000),(358450817/50000000000000),(-3255717/100000000000000)⟩
def e256 : ℝ := (774493/25000000000000)
theorem h256 : Model (fun x => f256 ((79/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(497772149293/5000000000000),(290756919349/100000000000000),(358450817/50000000000000),(-3255717/100000000000000)⟩
def e257 : ℝ := (774493/25000000000000)
theorem h257 : Model (fun x => f257 ((79/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(202893972176289/50000000000000),(1073031488073/100000000000000),(2645708411/100000000000000),(-12015147/100000000000000)⟩
def e258 : ℝ := (2286599/20000000000000)
theorem h258 : Model (fun x => f258 ((79/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2761502230066863/100000000000000),(1073031488073/100000000000000),(2645708411/100000000000000),(-12015147/100000000000000)⟩
def e259 : ℝ := (2858249/25000000000000)
theorem h259 : Model (fun x => f259 ((79/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3036422010134421/100000000000000),(35973106789/390625000000),(3228283539/12500000000000),(-43866423/50000000000000)⟩
def e260 : ℝ := (19647899/20000000000000)
theorem h260 : Model (fun x => f260 ((79/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8318802962515373/100000000000000),(35973106789/390625000000),(3228283539/12500000000000),(-43866423/50000000000000)⟩
def e261 : ℝ := (12279937/12500000000000)
theorem h261 : Model (fun x => f261 ((79/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(9146976648554623/100000000000000),(17156709392741/50000000000000),(14351395269/12500000000000),(-113095881/50000000000000)⟩
def e262 : ℝ := (73335509/20000000000000)
theorem h262 : Model (fun x => f262 ((79/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7208012133801121/50000000000000),(17156709392741/50000000000000),(14351395269/12500000000000),(-113095881/50000000000000)⟩
def e263 : ℝ := (183338773/50000000000000)
theorem h263 : Model (fun x => f263 ((79/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(3962800836097781/25000000000000),(39822529841127/50000000000000),(329358474857/100000000000000),(-138240249/100000000000000)⟩
def e264 : ℝ := (426439397/50000000000000)
theorem h264 : Model (fun x => f264 ((79/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(18186917630105409/100000000000000),(39822529841127/50000000000000),(329358474857/100000000000000),(-138240249/100000000000000)⟩
def e265 : ℝ := (170575759/20000000000000)
theorem h265 : Model (fun x => f265 ((79/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(19997505845655873/100000000000000),(140453799615809/100000000000000),(14482068033/2000000000000),(392246021/50000000000000)⟩
def e266 : ℝ := (1506821341/100000000000000)
theorem h266 : Model (fun x => f266 ((79/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(815995471921473/4000000000000),(140453799615809/100000000000000),(14482068033/2000000000000),(392246021/50000000000000)⟩
def e267 : ℝ := (753410671/50000000000000)
theorem h267 : Model (fun x => f267 ((79/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(11215392948697681/50000000000000),(21375067996269/10000000000000),(67540868281/5000000000000),(662145089/20000000000000)⟩
def e268 : ℝ := (2300497899/100000000000000)
theorem h268 : Model (fun x => f268 ((79/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(11206583424888157/50000000000000),(21375067996269/10000000000000),(67540868281/5000000000000),(662145089/20000000000000)⟩
def e269 : ℝ := (23004979/1000000000000)
theorem h269 : Model (fun x => f269 ((79/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(6161124224207867/25000000000000),(37524792562403/12500000000000),(2267472469821/100000000000000),(8370590621/100000000000000)⟩
def e270 : ℝ := (649923421/20000000000000)
theorem h270 : Model (fun x => f270 ((79/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(24647830230164801/100000000000000),(37524792562403/12500000000000),(2267472469821/100000000000000),(8370590621/100000000000000)⟩
def e271 : ℝ := (1624808553/50000000000000)
theorem h271 : Model (fun x => f271 ((79/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1226900342907811/50000000000000),(6346959156031/6250000000000),(1275285073391/100000000000000),(4387912843/50000000000000)⟩
def e272 : ℝ := (1136773311/100000000000000)
theorem h272 : Model (fun x => f272 ((79/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(120901994422167/100000000000000),(159851529341/25000000000000),(605485149/25000000000000),(-1495397/50000000000000)⟩
def e273 : ℝ := (6844679/100000000000000)
theorem h273 : Model (fun x => f273 ((79/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(10497772149293/5000000000000),(290756919349/100000000000000),(358450817/50000000000000),(-3255717/100000000000000)⟩
def e274 : ℝ := (774493/25000000000000)
theorem h274 : Model (fun x => f274 ((79/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(440812880393887/100000000000000),(610459978031/50000000000000),(481967983/12500000000000),(-2375557/25000000000000)⟩
def e275 : ℝ := (13040623/100000000000000)
theorem h275 : Model (fun x => f275 ((79/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(462755317884857/50000000000000),(3845081853379/100000000000000),(1850681013/12500000000000),(-3584607/25000000000000)⟩
def e276 : ℝ := (8230329/20000000000000)
theorem h276 : Model (fun x => f276 ((79/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(60723748600361/3125000000000),(5381972425621/50000000000000),(24449843283/50000000000000),(5188501/50000000000000)⟩
def e277 : ℝ := (28843257/25000000000000)
theorem h277 : Model (fun x => f277 ((79/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(2349319140663653/100000000000000),(25438507627443/100000000000000),(175008197973/100000000000000),(131948507/25000000000000)⟩
def e278 : ℝ := (137450963/50000000000000)
theorem h278 : Model (fun x => f278 ((79/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(5497772149293/625000000000),(290756919349/12500000000000),(358450817/6250000000000),(-3255717/12500000000000)⟩
def e279 : ℝ := (774493/3125000000000)
theorem h279 : Model (fun x => f279 ((79/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(1000545538309047/100000000000000),(741365368039/25000000000000),(2039288417/25000000000000),(-2903653/10000000000000)⟩
def e280 : ℝ := (6325691/20000000000000)
theorem h280 : Model (fun x => f280 ((79/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1100545538309047/100000000000000),(741365368039/25000000000000),(2039288417/25000000000000),(-2903653/10000000000000)⟩
def e281 : ℝ := (6325691/20000000000000)
theorem h281 : Model (fun x => f281 ((79/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(25855326983214277/100000000000000),(349630514680597/100000000000000),(574410325941/20000000000000),(12391311711/100000000000000)⟩
def e282 : ℝ := (951824733/25000000000000)
theorem h282 : Model (fun x => f282 ((79/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(386767493077/100000000000000),(-5230091183/100000000000000),(27761523/100000000000000),(20199/100000000000000)⟩
def e283 : ℝ := (29703/50000000000000)
theorem h283 : Model (fun x => f283 ((79/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (6375702054573333/25000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(1898100679527/20000000000000),(264431583713/100000000000000),(30237253/10000000000000),(-254293/6250000000000)⟩
def e284 : ℝ := (3031183/50000000000000)
theorem h284 : Model (fun x => f284 ((79/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(119910885971721/50000000000000),(290756919349/25000000000000),(358450817/12500000000000),(-6511433/50000000000000)⟩
def e285 : ℝ := (3097971/25000000000000)
theorem h285 : Model (fun x => f285 ((79/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(45472964904911/100000000000000),(-60122440647/50000000000000),(21484961/100000000000000),(1036801/50000000000000)⟩
def e286 : ℝ := (1297217/100000000000000)
theorem h286 : Model (fun x => f286 ((79/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (10966396281119/5000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(109054070190177/100000000000000),(120244881293/50000000000000),(-42969923/100000000000000),(-4147209/100000000000000)⟩
def e287 : ℝ := (1763289/20000000000000)
theorem h287 : Model (fun x => f287 ((79/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(9054070190177/100000000000000),(120244881293/50000000000000),(-42969923/100000000000000),(-4147209/100000000000000)⟩
def e288 : ℝ := (1763289/20000000000000)
theorem h288 : Model (fun x => f288 ((79/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(402461449511367/100000000000000),(221880435719/25000000000000),(-79289739/50000000000000),(-15305177/100000000000000)⟩
def e289 : ℝ := (32536883/100000000000000)
theorem h289 : Model (fun x => f289 ((79/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(689543933806413/25000000000000),(221880435719/25000000000000),(-79289739/50000000000000),(-15305177/100000000000000)⟩
def e290 : ℝ := (8134221/25000000000000)
theorem h290 : Model (fun x => f290 ((79/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(3007902902261413/100000000000000),(7601008861777/100000000000000),(776275567/100000000000000),(-65920483/50000000000000)⟩
def e291 : ℝ := (55777187/20000000000000)
theorem h291 : Model (fun x => f291 ((79/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(1658056770928473/20000000000000),(7601008861777/100000000000000),(776275567/100000000000000),(-65920483/50000000000000)⟩
def e292 : ℝ := (17430371/6250000000000)
theorem h292 : Model (fun x => f292 ((79/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(2260222993451649/25000000000000),(14113246749509/50000000000000),(7781939839/50000000000000),(-488992623/100000000000000)⟩
def e293 : ℝ := (259254627/25000000000000)
theorem h293 : Model (fun x => f293 ((79/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(2861987918570843/20000000000000),(14113246749509/50000000000000),(7781939839/50000000000000),(-488992623/100000000000000)⟩
def e294 : ℝ := (1037018509/100000000000000)
theorem h294 : Model (fun x => f294 ((79/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(3901392891940791/25000000000000),(65196079785699/100000000000000),(39352950723/50000000000000),(-1101428827/100000000000000)⟩
def e295 : ℝ := (2399877073/100000000000000)
theorem h295 : Model (fun x => f295 ((79/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(17941285853477449/100000000000000),(65196079785699/100000000000000),(39352950723/50000000000000),(-1101428827/100000000000000)⟩
def e296 : ℝ := (1199938537/50000000000000)
theorem h296 : Model (fun x => f296 ((79/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(19565702467671593/100000000000000),(114245934364643/100000000000000),(117456264891/50000000000000),(-891975329/50000000000000)⟩
def e297 : ℝ := (2107932171/50000000000000)
theorem h297 : Model (fun x => f297 ((79/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(3993616684010509/20000000000000),(114245934364643/100000000000000),(117456264891/50000000000000),(-891975329/50000000000000)⟩
def e298 : ℝ := (4215864343/100000000000000)
theorem h298 : Model (fun x => f298 ((79/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(10888003854268599/50000000000000),(1726110378613/1000000000000),(522351181361/100000000000000),(-2257739761/100000000000000)⟩
def e299 : ℝ := (6387419361/100000000000000)
theorem h299 : Model (fun x => f299 ((79/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(435167773218363/2000000000000),(1726110378613/1000000000000),(522351181361/100000000000000),(-2257739761/100000000000000)⟩
def e300 : ℝ := (3193709681/50000000000000)
theorem h300 : Model (fun x => f300 ((79/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(2966051055316149/12500000000000),(60141514904609/25000000000000),(7620371377/781250000000),(-2182492671/100000000000000)⟩
def e301 : ℝ := (2231879913/25000000000000)
theorem h301 : Model (fun x => f301 ((79/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(949269671034501/4000000000000),(60141514904609/25000000000000),(7620371377/781250000000),(-2182492671/100000000000000)⟩
def e302 : ℝ := (8927519653/100000000000000)
theorem h302 : Model (fun x => f302 ((79/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(42973771154763/2000000000000),(7885342934589/10000000000000),(164163329361/25000000000000),(265143717/25000000000000)⟩
def e303 : ℝ := (739763593/25000000000000)
theorem h303 : Model (fun x => f303 ((79/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(2973197556261/2500000000000),(524527748981/100000000000000),(484632359/100000000000000),(-9252077/100000000000000)⟩
def e304 : ℝ := (19291733/100000000000000)
theorem h304 : Model (fun x => f304 ((79/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(209054070190177/100000000000000),(120244881293/50000000000000),(-42969923/100000000000000),(-4147209/100000000000000)⟩
def e305 : ℝ := (1763289/20000000000000)
theorem h305 : Model (fun x => f305 ((79/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(218518021315397/50000000000000),(1005507274153/100000000000000),(398692513/100000000000000),(-3509299/20000000000000)⟩
def e306 : ℝ := (36924623/100000000000000)
theorem h306 : Model (fun x => f306 ((79/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(913641635317751/100000000000000),(3153080824013/100000000000000),(3063830931/100000000000000),(-1696241/3125000000000)⟩
def e307 : ℝ := (115985059/100000000000000)
theorem h307 : Model (fun x => f307 ((79/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(477501256395963/25000000000000),(8788858398647/100000000000000),(2719061749/20000000000000),(-145351253/100000000000000)⟩
def e308 : ℝ := (80960547/25000000000000)
theorem h308 : Model (fun x => f308 ((79/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(454305781960971/20000000000000),(20470911291391/100000000000000),(35762559513/50000000000000),(-117836757/50000000000000)⟩
def e309 : ℝ := (758521919/100000000000000)
theorem h309 : Model (fun x => f309 ((79/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(109054070190177/12500000000000),(120244881293/6250000000000),(-42969923/12500000000000),(-4147209/12500000000000)⟩
def e310 : ℝ := (1763289/2500000000000)
theorem h310 : Model (fun x => f310 ((79/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(61960028985741/6250000000000),(2448445849669/100000000000000),(5634919/4000000000000),(-42429749/100000000000000)⟩
def e311 : ℝ := (89823293/100000000000000)
theorem h311 : Model (fun x => f311 ((79/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(68210028985741/6250000000000),(2448445849669/100000000000000),(5634919/4000000000000),(-42429749/100000000000000)⟩
def e312 : ℝ := (89823293/100000000000000)
theorem h312 : Model (fun x => f312 ((79/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(495811368895161/2000000000000),(139514293862099/50000000000000),(321254004743/25000000000000),(-1755759781/100000000000000)⟩
def e313 : ℝ := (10369982693/100000000000000)
theorem h313 : Model (fun x => f313 ((79/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(630280021/156250000000),(-4540207801/100000000000000),(15096447/50000000000000),(-3037/4000000000000)⟩
def e314 : ℝ := (173651/100000000000000)
theorem h314 : Model (fun x => f314 ((79/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (12255121357636203/50000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(8667363003479/100000000000000),(55130854387/25000000000000),(-56511061/20000000000000),(-3358547/100000000000000)⟩
def e315 : ℝ := (4007793/25000000000000)
theorem h315 : Model (fun x => f315 ((79/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(9078933200557/50000000000000),(484955001261/100000000000000),(792689/4000000000000),(-1485447/20000000000000)⟩
def e316 : ℝ := (11046769/50000000000000)
theorem h316 : Model (fun x => f316 ((79/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(82599033328497/100000000000000),(1956369009861/100000000000000),(-367017379/5000000000000),(-12562177/20000000000000)⟩
def e317 : ℝ := (101623997/100000000000000)
theorem h317 : Model (fun x => f317 ((79/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(209111476781/500000000000),(461170443521/100000000000000),(-4777116119/50000000000000),(22284167/25000000000000)⟩
def e318 : ℝ := (55432797/100000000000000)
theorem h318 : Model (fun x => f318 ((79/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-12533871345987/12500000000000),(-176563292299/20000000000000),(8927581797/50000000000000),(-38225093/12500000000000)⟩
def e319 : ℝ := (24204259/25000000000000)
theorem h319 : Model (fun x => f319 ((79/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((79/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-68651/1600),(-869/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((79/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((79/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(7663/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((79/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(237869/1600),(1071/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((79/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((79/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(410669/1600),(1071/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((79/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2053345/32),(5355/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((79/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((79/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(127635709316070167/12500000000000),(3751468493720239/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (66157/50000000000000)
theorem h329 : Model (fun x => f329 ((79/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9793497499/100000000000000),(-8995327/25000000000000),(570991/100000000000000),(-371/10000000000000)⟩
def e330 : ℝ := (21/50000000000000)
theorem h330 : Model (fun x => f330 ((79/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (508644228209465853/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(628419660065129/100000000000000),(60559217459/6250000000000),(1940932373/25000000000000),(14886737/100000000000000)⟩
def e331 : ℝ := (2469303/50000000000000)
theorem h331 : Model (fun x => f331 ((79/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((79/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(439/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((79/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((79/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((79/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(645806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((79/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((79/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((79/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1432557938127551/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (263/25000000000000)
theorem h339 : Model (fun x => f339 ((79/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3744193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((79/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((79/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((79/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2109884123744639/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (263/25000000000000)
theorem h343 : Model (fun x => f343 ((79/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4739596780439/100000000000000),(-3164631439/50000000000000),(1056513/12500000000000),(-11287/100000000000000)⟩
def e344 : ℝ := (1/5000000000000)
theorem h344 : Model (fun x => f344 ((79/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1053533291054553/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(135794939826833/100000000000000),(435009183473/50000000000000),(-116182353/10000000000000),(775749/50000000000000)⟩
def e345 : ℝ := (627/20000000000000)
theorem h345 : Model (fun x => f345 ((79/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(235794939826833/100000000000000),(435009183473/50000000000000),(-116182353/10000000000000),(775749/50000000000000)⟩
def e346 : ℝ := (627/20000000000000)
theorem h346 : Model (fun x => f346 ((79/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(14737183739177/12500000000000),(435009183473/100000000000000),(-116182353/20000000000000),(775749/100000000000000)⟩
def e347 : ℝ := (49/3125000000000)
theorem h347 : Model (fun x => f347 ((79/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(2237183739177/12500000000000),(435009183473/100000000000000),(-116182353/20000000000000),(775749/100000000000000)⟩
def e348 : ℝ := (49/3125000000000)
theorem h348 : Model (fun x => f348 ((79/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(108774451408211/25000000000000),(321078206849/20000000000000),(-1071920519/50000000000000),(2862883/100000000000000)⟩
def e349 : ℝ := (5789/100000000000000)
theorem h349 : Model (fun x => f349 ((79/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2790812091347129/100000000000000),(321078206849/20000000000000),(-1071920519/50000000000000),(2862883/100000000000000)⟩
def e350 : ℝ := (579/10000000000000)
theorem h350 : Model (fun x => f350 ((79/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3290296845735957/100000000000000),(7016502151213/50000000000000),(-11756091691/100000000000000),(199161/3125000000000)⟩
def e351 : ℝ := (44017/50000000000000)
theorem h351 : Model (fun x => f351 ((79/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8572677798116909/100000000000000),(7016502151213/50000000000000),(-11756091691/100000000000000),(199161/3125000000000)⟩
def e352 : ℝ := (17607/20000000000000)
theorem h352 : Model (fun x => f352 ((79/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(631685639238061/6250000000000),(1345912317919/2500000000000),(-2614971137/100000000000000),(-11728641/20000000000000)⟩
def e353 : ℝ := (221911/50000000000000)
theorem h353 : Model (fun x => f353 ((79/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(3075203569371319/20000000000000),(1345912317919/2500000000000),(-2614971137/100000000000000),(-11728641/20000000000000)⟩
def e354 : ℝ := (443823/100000000000000)
theorem h354 : Model (fun x => f354 ((79/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(4531984003719807/25000000000000),(65179476244727/50000000000000),(141789605907/100000000000000),(-54795487/20000000000000)⟩
def e355 : ℝ := (37807/4000000000000)
theorem h355 : Model (fun x => f355 ((79/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(20463650300593513/100000000000000),(65179476244727/50000000000000),(141789605907/100000000000000),(-54795487/20000000000000)⟩
def e356 : ℝ := (118147/12500000000000)
theorem h356 : Model (fun x => f356 ((79/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(24126125956328899/100000000000000),(3033858310901/1250000000000),(153841005157/25000000000000),(-304738587/100000000000000)⟩
def e357 : ℝ := (2448309/100000000000000)
theorem h357 : Model (fun x => f357 ((79/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(24528506908709851/100000000000000),(3033858310901/1250000000000),(153841005157/25000000000000),(-304738587/100000000000000)⟩
def e358 : ℝ := (244831/10000000000000)
theorem h358 : Model (fun x => f358 ((79/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(28918489052906361/100000000000000),(392848632766511/100000000000000),(204851826243/12500000000000),(8783739/800000000000)⟩
def e359 : ℝ := (1577421/25000000000000)
theorem h359 : Model (fun x => f359 ((79/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(28900870005287313/100000000000000),(392848632766511/100000000000000),(204851826243/12500000000000),(8783739/800000000000)⟩
def e360 : ℝ := (1261937/20000000000000)
theorem h360 : Model (fun x => f360 ((79/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(17036697259599539/50000000000000),(147220009311939/25000000000000),(3473160037329/100000000000000),(1591391023/25000000000000)⟩
def e361 : ℝ := (962843/10000000000000)
theorem h361 : Model (fun x => f361 ((79/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(34076727852532411/100000000000000),(147220009311939/25000000000000),(3473160037329/100000000000000),(1591391023/25000000000000)⟩
def e362 : ℝ := (9628431/100000000000000)
theorem h362 : Model (fun x => f362 ((79/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(3049436057441819/50000000000000),(253631523078147/100000000000000),(298533429317/10000000000000),(6545658247/50000000000000)⟩
def e363 : ℝ := (14401909/100000000000000)
theorem h363 : Model (fun x => f363 ((79/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(17374766764981/12500000000000),(1025729642411/100000000000000),(10451387/2000000000000),(-3224863/100000000000000)⟩
def e364 : ℝ := (6923/50000000000000)
theorem h364 : Model (fun x => f364 ((79/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(27237183739177/12500000000000),(435009183473/100000000000000),(-116182353/20000000000000),(775749/100000000000000)⟩
def e365 : ℝ := (49/3125000000000)
theorem h365 : Model (fun x => f365 ((79/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(11869826848667/2500000000000),(1895748009357/100000000000000),(-31962709/5000000000000),(-334673/20000000000000)⟩
def e366 : ℝ := (8491/50000000000000)
theorem h366 : Model (fun x => f366 ((79/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(20691241909079/2000000000000),(1549045105621/25000000000000),(163825217/4000000000000),(-1719557/12500000000000)⟩
def e367 : ℝ := (557/1000000000000)
theorem h367 : Model (fun x => f367 ((79/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(17611598677167/781250000000),(9000880247909/50000000000000),(14934168003/50000000000000),(-20063669/50000000000000)⟩
def e368 : ℝ := (173613/100000000000000)
theorem h368 : Model (fun x => f368 ((79/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(3133413574392059/100000000000000),(12036244219771/25000000000000),(59486505961/25000000000000),(33995777/12500000000000)⟩
def e369 : ℝ := (1394949/100000000000000)
theorem h369 : Model (fun x => f369 ((79/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(14737183739177/1562500000000),(435009183473/12500000000000),(-116182353/2500000000000),(775749/12500000000000)⟩
def e370 : ℝ := (49/390625000000)
theorem h370 : Model (fun x => f370 ((79/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(135272236678397/12500000000000),(901160622039/20000000000000),(-412472477/10000000000000),(2981129/100000000000000)⟩
def e371 : ℝ := (2639/10000000000000)
theorem h371 : Model (fun x => f371 ((79/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(147772236678397/12500000000000),(901160622039/20000000000000),(-412472477/10000000000000),(2981129/100000000000000)⟩
def e372 : ℝ := (2639/10000000000000)
theorem h372 : Model (fun x => f372 ((79/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(37042522586109221/100000000000000),(142068943950077/20000000000000),(4853018471943/100000000000000),(602203357/5000000000000)⟩
def e373 : ℝ := (21272409/100000000000000)
theorem h373 : Model (fun x => f373 ((79/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(269960016269/100000000000000),(-5176879401/100000000000000),(6390623/10000000000000),(-317519/50000000000000)⟩
def e374 : ℝ := (233/4000000000000)
theorem h374 : Model (fun x => f374 ((79/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (2270457048909209/6250000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(3292903230713/20000000000000),(92243111689/25000000000000),(-1173429889/100000000000000),(4150353/100000000000000)⟩
def e375 : ℝ := (801083/100000000000000)
theorem h375 : Model (fun x => f375 ((79/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(135794939826833/50000000000000),(435009183473/25000000000000),(-116182353/5000000000000),(775749/25000000000000)⟩
def e376 : ℝ := (627/10000000000000)
theorem h376 : Model (fun x => f376 ((79/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(42409731130549/100000000000000),(-1956002801/1250000000000),(196583197/25000000000000),(-3951421/100000000000000)⟩
def e377 : ℝ := (20151/100000000000000)
theorem h377 : Model (fun x => f377 ((79/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (58730939520431/25000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(115180537738901/100000000000000),(62592089631/20000000000000),(-1572665579/100000000000000),(197571/2500000000000)⟩
def e378 : ℝ := (599/400000000000)
theorem h378 : Model (fun x => f378 ((79/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(15180537738901/100000000000000),(62592089631/20000000000000),(-1572665579/100000000000000),(197571/2500000000000)⟩
def e379 : ℝ := (599/400000000000)
theorem h379 : Model (fun x => f379 ((79/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(212535516065829/50000000000000),(288743270619/25000000000000),(-46431079/800000000000),(14582621/50000000000000)⟩
def e380 : ℝ := (138163/25000000000000)
theorem h380 : Model (fun x => f380 ((79/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2780785317845943/100000000000000),(288743270619/25000000000000),(-46431079/800000000000),(14582621/50000000000000)⟩
def e381 : ℝ := (552653/100000000000000)
theorem h381 : Model (fun x => f381 ((79/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(800730870614841/25000000000000),(5016531200047/50000000000000),(-23401395197/50000000000000),(13564123/6250000000000)⟩
def e382 : ℝ := (5079001/100000000000000)
theorem h382 : Model (fun x => f382 ((79/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2121326108710079/25000000000000),(5016531200047/50000000000000),(-23401395197/50000000000000),(13564123/6250000000000)⟩
def e383 : ℝ := (2539501/50000000000000)
theorem h383 : Model (fun x => f383 ((79/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(977341927683189/10000000000000),(381117820107/1000000000000),(-77976825361/50000000000000),(77036371/12500000000000)⟩
def e384 : ℝ := (260039/1250000000000)
theorem h384 : Model (fun x => f384 ((79/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(15042466895879509/100000000000000),(381117820107/1000000000000),(-77976825361/50000000000000),(77036371/12500000000000)⟩
def e385 : ℝ := (20803121/100000000000000)
theorem h385 : Model (fun x => f385 ((79/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(17325994259870187/100000000000000),(45487163636357/50000000000000),(-296921148849/100000000000000),(40559261/5000000000000)⟩
def e386 : ℝ := (54025339/100000000000000)
theorem h386 : Model (fun x => f386 ((79/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(2457713568198059/12500000000000),(45487163636357/50000000000000),(-296921148849/100000000000000),(40559261/5000000000000)⟩
def e387 : ℝ := (2701267/5000000000000)
theorem h387 : Model (fun x => f387 ((79/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(4529292326291929/20000000000000),(133054472429/80000000000),(-183247318053/50000000000000),(128193177/100000000000000)⟩
def e388 : ℝ := (13301351/12500000000000)
theorem h388 : Model (fun x => f388 ((79/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(23048842583840597/100000000000000),(133054472429/80000000000),(-183247318053/50000000000000),(128193177/100000000000000)⟩
def e389 : ℝ := (106410809/100000000000000)
theorem h389 : Model (fun x => f389 ((79/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(26547780830660403/100000000000000),(65924958020413/25000000000000),(-13205093241/5000000000000),(-448360969/25000000000000)⟩
def e390 : ℝ := (88502137/50000000000000)
theorem h390 : Model (fun x => f390 ((79/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(5306032356608271/20000000000000),(65924958020413/25000000000000),(-13205093241/5000000000000),(-448360969/25000000000000)⟩
def e391 : ℝ := (7080171/4000000000000)
theorem h391 : Model (fun x => f391 ((79/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(15278791502353719/50000000000000),(193379898910339/50000000000000),(103851505773/100000000000000),(-2471356467/50000000000000)⟩
def e392 : ℝ := (52788671/20000000000000)
theorem h392 : Model (fun x => f392 ((79/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(30560916338040771/100000000000000),(193379898910339/50000000000000),(103851505773/100000000000000),(-2471356467/50000000000000)⟩
def e393 : ℝ := (65985839/25000000000000)
theorem h393 : Model (fun x => f393 ((79/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(14497848243907/312500000000),(19294474724859/12500000000000),(745549401693/100000000000000),(-2046287079/50000000000000)⟩
def e394 : ℝ := (100791907/100000000000000)
theorem h394 : Model (fun x => f394 ((79/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(132665562738223/100000000000000),(72093905419/10000000000000),(-2643366921/100000000000000),(522589/6250000000000)⟩
def e395 : ℝ := (210179/50000000000000)
theorem h395 : Model (fun x => f395 ((79/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(215180537738901/100000000000000),(62592089631/20000000000000),(-1572665579/100000000000000),(197571/2500000000000)⟩
def e396 : ℝ := (599/400000000000)
theorem h396 : Model (fun x => f396 ((79/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(18521065528641/4000000000000),(2693719901/200000000000),(-5788698079/100000000000000),(377611/1562500000000)⟩
def e397 : ℝ := (359929/50000000000000)
theorem h397 : Model (fun x => f397 ((79/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(498171604993799/50000000000000),(4347270726113/100000000000000),(-15522873279/100000000000000),(2464861/5000000000000)⟩
def e398 : ℝ := (2520619/100000000000000)
theorem h398 : Model (fun x => f398 ((79/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(107196833848817/5000000000000),(6236320350277/50000000000000),(-443326387/1250000000000),(16967237/25000000000000)⟩
def e399 : ℝ := (3837169/50000000000000)
theorem h399 : Model (fun x => f399 ((79/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2844265657261819/100000000000000),(8000843943783/25000000000000),(-6901645357/50000000000000),(-158042173/50000000000000)⟩
def e400 : ℝ := (10887987/50000000000000)
theorem h400 : Model (fun x => f400 ((79/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(115180537738901/12500000000000),(62592089631/2500000000000),(-1572665579/12500000000000),(197571/312500000000)⟩
def e401 : ℝ := (599/50000000000)
theorem h401 : Model (fun x => f401 ((79/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1054109864649431/100000000000000),(322462263943/10000000000000),(-15224691553/100000000000000),(4474009/6250000000000)⟩
def e402 : ℝ := (809179/50000000000000)
theorem h402 : Model (fun x => f402 ((79/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1154109864649431/100000000000000),(322462263943/10000000000000),(-15224691553/100000000000000),(4474009/6250000000000)⟩
def e403 : ℝ := (809179/50000000000000)
theorem h403 : Model (fun x => f403 ((79/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(8206487631823657/25000000000000),(461070951151221/100000000000000),(13739133987/3125000000000),(-173235917/2500000000000)⟩
def e404 : ℝ := (313429541/100000000000000)
theorem h404 : Model (fun x => f404 ((79/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(152318513849/50000000000000),(-4278909883/100000000000000),(448169/800000000000),(-166313/25000000000000)⟩
def e405 : ℝ := (2163/20000000000000)
theorem h405 : Model (fun x => f405 ((79/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (16182216340494801/50000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(14133060470529/100000000000000),(67928239717/25000000000000),(-173453149/10000000000000),(5619929/50000000000000)⟩
def e406 : ℝ := (127129/10000000000000)
theorem h406 : Model (fun x => f406 ((79/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(15298788312047/50000000000000),(80085675703/12500000000000),(-2907961379/100000000000000),(15390211/100000000000000)⟩
def e407 : ℝ := (2072373/100000000000000)
theorem h407 : Model (fun x => f407 ((79/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(96140593504649/50000000000000),(1080666873887/25000000000000),(-1938156569/20000000000000),(24566911/20000000000000)⟩
def e408 : ℝ := (7302911/50000000000000)
theorem h408 : Model (fun x => f408 ((79/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(48678781521341/50000000000000),(478159093539/50000000000000),(-17012019/100000000000),(138768361/50000000000000)⟩
def e409 : ℝ := (16111521/100000000000000)
theorem h409 : Model (fun x => f409 ((79/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-1456703862607/50000000000000),(73501725583/100000000000000),(421572297/50000000000000),(-14132011/50000000000000)⟩
def e410 : ℝ := (112928557/100000000000000)
theorem h410 : Model (fun x => f410 ((79/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(4526425428710937/100000000000000),(66805821533203/25000000000000),(642823/10240000),(1501/2048000)⟩
def e411 : ℝ := (425781251/100000000000000)
theorem h411 : Model (fun x => f411 ((79/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(39601/1600),(199/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((79/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(7880599/64000),(118803/64000),(597/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((79/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(557358495423030959/100000000000000),(20653378763141387/50000000000000),(655626585771087/50000000000000),(4648218079663/20000000000000)⟩
def e414 : ℝ := (126394372889/50000000000000)
theorem h414 : Model (fun x => f414 ((79/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(17941773709/100000000000000),(-1329694447/100000000000000),(56335659/100000000000000),(-179501/10000000000000)⟩
def e415 : ℝ := (36091/50000000000000)
theorem h415 : Model (fun x => f415 ((79/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (257358495423030959/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2844018828017/50000000000000),(2222706947/20000000000000),(-3372887/312500000000),(2377313/10000000000000)⟩
def e416 : ℝ := (44774519/100000000000000)
theorem h416 : Model (fun x => f416 ((79/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(138731496541/5000000000000),(42307630159/50000000000000),(-118089623/50000000000000),(-1122723/25000000000000)⟩
def e417 : ℝ := (39425769/25000000000000)
theorem h417 : Model (fun x => f417 ((79/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((79/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((4161590251993/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (39/20) 2 ∧
    SigmaActualBlockSeparable.endpointCellMass (39/20) 2 ≤ (4162063361221/3000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(79/40)-(1/40)) (by norm_num : ((79/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel19


noncomputable section
namespace Hf4Quad.Panel20
open Hf4Quad.Dag

def p0 : Cubic := ⟨(81/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((81/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((81/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((81/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((81/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(177428571428571/50000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((81/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-177428571428571/50000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((81/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-263428571428571/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((81/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((81/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(6561/1600),(81/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((81/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(99282857142857/20000000000000),(6128571428571/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((81/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-99282857142857/20000000000000),(-6128571428571/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((81/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-94980357142857/12500000000000),(-8319047619047/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((81/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((81/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(531441/64000),(19683/64000),(243/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((81/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(103552263/1280000),(3835269/1280000),(47349/1280000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/100000000000000)
theorem h14 : Model (fun x => f14 ((81/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-103552263/1280000),(-3835269/1280000),(-47349/1280000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/100000000000000)
theorem h15 : Model (fun x => f15 ((81/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-138279115687779/1562500000000),(-158134242931547/50000000000000),(-3774802000661/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((81/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((81/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(43046721/2560000),(531441/640000),(19683/1280000),(81/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((81/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(2348779419642857/50000000000000),(115989107142857/50000000000000),(2147946428571/50000000000000),(35357142857/100000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((81/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-2076152282366071/50000000000000),(-4214513578869/5000000000000),(521090856481/100000000000000),(5033585483/25000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((81/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((81/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(1702531445800781/50000000000000),(52547266845703/25000000000000),(531441/10240000),(6561/10240000)⟩
def e22 : ℝ := (49560547/12500000000000)
theorem h22 : Model (fun x => f22 ((81/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(22183354171582027/100000000000000),(342335712524413/25000000000000),(4226366821289/12500000000000),(13044342041/3125000000000)⟩
def e23 : ℝ := (258302229/10000000000000)
theorem h23 : Model (fun x => f23 ((81/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(3606209921369977/20000000000000),(80315786157517/6250000000000),(34332025426793/100000000000000),(109388321811/25000000000000)⟩
def e24 : ℝ := (1346074641/50000000000000)
theorem h24 : Model (fun x => f24 ((81/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((81/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(6895252355493163/100000000000000),(510759433740233/100000000000000),(1576418005371/10000000000000),(259492675781/100000000000000)⟩
def e26 : ℝ := (2414599613/100000000000000)
theorem h26 : Model (fun x => f26 ((81/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(3096661481133649/20000000000000),(573455829839563/50000000000000),(7079701602957/20000000000000),(291345744977/50000000000000)⟩
def e27 : ℝ := (2710994911/50000000000000)
theorem h27 : Model (fun x => f27 ((81/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(3351435701251813/10000000000000),(1215982119099699/50000000000000),(34865266720789/50000000000000),(510122388599/50000000000000)⟩
def e28 : ℝ := (253566847/3125000000000)
theorem h28 : Model (fun x => f28 ((81/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((81/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(2792577203974731/20000000000000),(12066691622113/1000000000000),(11172862613067/25000000000000),(919577169799/100000000000000)⟩
def e30 : ℝ := (11437246103/100000000000000)
theorem h30 : Model (fun x => f30 ((81/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(82835375395679/2500000000000),(143172253770309/50000000000000),(10605352131133/100000000000000),(218217122039/100000000000000)⟩
def e31 : ℝ := (2714076657/100000000000000)
theorem h31 : Model (fun x => f31 ((81/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(3682777202834529/10000000000000),(169894296608751/6250000000000),(80335885572711/100000000000000),(1238461899237/100000000000000)⟩
def e32 : ℝ := (10828215761/100000000000000)
theorem h32 : Model (fun x => f32 ((81/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((81/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(2814669/320),(34749/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((81/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((81/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(178929/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((81/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(5677533/320),(52421/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((81/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((81/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(6407133/320),(52421/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((81/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-6407133/320),(-52421/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((81/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((81/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(121/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((81/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(14641/1600),(121/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((81/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((81/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(307461/160),(2541/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((81/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(6504890051/12500000000000),(-860150751/100000000000000),(426521/4000000000000),(-117499/100000000000000)⟩
def e46 : ℝ := (249/20000000000000)
theorem h46 : Model (fun x => f46 ((81/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (151179/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-208388478535669/20000000000000),(8627312483/5000000000000),(-1450865551/100000000000000),(12198517/100000000000000)⟩
def e47 : ℝ := (49696073/100000000000000)
theorem h47 : Model (fun x => f47 ((81/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((81/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(161/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((81/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((81/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((81/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(26833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((81/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(46833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((81/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((81/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(29270833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((81/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((81/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(614687499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((81/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((81/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(4270833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((81/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(84007291666659/20000000000000),(5869791666657/50000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (23/20000000000000)
theorem h60 : Model (fun x => f60 ((81/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(137085069444441/100000000000000),(487847222221/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((81/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((81/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(29270833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((81/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1307918402777761/100000000000000),(2571180555551/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((81/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1407918402777761/100000000000000),(2571180555551/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((81/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(2956885297625201/50000000000000),(9344177282247/5000000000000),(562143825951/50000000000000),(415726273/20000000000000)⟩
def e66 : ℝ := (126961/20000000000000)
theorem h66 : Model (fun x => f66 ((81/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(54270833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((81/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(94250347222221/20000000000000),(904513888887/50000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((81/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(15984515267831/1562500000000),(5890646701377/100000000000000),(1130642361/10000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (63/100000000000000)
theorem h69 : Model (fun x => f69 ((81/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(12099680815389449/20000000000000),(2260194781243599/100000000000000),(23178848979619/100000000000000),(34896011/32000000000)⟩
def e70 : ℝ := (67483063/25000000000000)
theorem h70 : Model (fun x => f70 ((81/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((81/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2878786458333261/12500000000000),(10244791666641/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((81/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(3934341493055149/100000000000000),(61980989583219/50000000000000),(366406249997/50000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1253/100000000000000)
theorem h73 : Model (fun x => f73 ((81/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(20124333332672333/50000000000000),(187487541562013/12500000000000),(15243733212749/100000000000000),(69900064831/100000000000000)⟩
def e74 : ℝ := (163615717/100000000000000)
theorem h74 : Model (fun x => f74 ((81/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(100747070742291911/100000000000000),(3760095113739703/100000000000000),(2401411387023/6250000000000),(89475049603/50000000000000)⟩
def e75 : ℝ := (433547969/100000000000000)
theorem h75 : Model (fun x => f75 ((81/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((81/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(959595486111087/12500000000000),(3414930555547/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((81/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(2918402777777/100000000000000),(14236111111/10000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((81/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(62320059317/12500000000000),(18240017361/50000000000000),(55609809/6250000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((81/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(38273310473451/100000000000000),(3072894035917/100000000000000),(44360768493/50000000000000),(1076941447/100000000000000)⟩
def e80 : ℝ := (2412389/50000000000000)
theorem h80 : Model (fun x => f80 ((81/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(41542489076391/50000000000000),(3415106464971/50000000000000),(205403395023/100000000000000),(2707533461/100000000000000)⟩
def e81 : ℝ := (14981153/100000000000000)
theorem h81 : Model (fun x => f81 ((81/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(100830155720444693/100000000000000),(753385065333929/20000000000000),(38627985587391/100000000000000),(181657632667/100000000000000)⟩
def e82 : ℝ := (224264561/50000000000000)
theorem h82 : Model (fun x => f82 ((81/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(85170747733/100000000000000),(4154670621/50000000000000),(304000289/100000000000000),(2471547/50000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((81/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(14550002737/100000000000000),(1774390577/100000000000000),(86555637/100000000000000),(2111113/100000000000000)⟩
def e84 : ℝ := (12937/50000000000000)
theorem h84 : Model (fun x => f84 ((81/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(2485625467/100000000000000),(90937517/25000000000000),(11089941/50000000000000),(45081/6250000000000)⟩
def e85 : ℝ := (13327/100000000000000)
theorem h85 : Model (fun x => f85 ((81/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(424627683/100000000000000),(72497409/100000000000000),(331543/6250000000000),(215637/100000000000000)⟩
def e86 : ℝ := (5341/100000000000000)
theorem h86 : Model (fun x => f86 ((81/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(1273883049/100000000000000),(217492227/100000000000000),(994629/6250000000000),(646911/100000000000000)⟩
def e87 : ℝ := (16023/100000000000000)
theorem h87 : Model (fun x => f87 ((81/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-1273883049/100000000000000),(-217492227/100000000000000),(-994629/6250000000000),(-646911/100000000000000)⟩
def e88 : ℝ := (16023/100000000000000)
theorem h88 : Model (fun x => f88 ((81/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(25207538611640411/25000000000000),(1883462554588709/50000000000000),(38627969673327/100000000000000),(45414246439/25000000000000)⟩
def e89 : ℝ := (89709029/20000000000000)
theorem h89 : Model (fun x => f89 ((81/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2878786458333261/10000000000000),(10244791666641/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((81/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1110390993938653/50000000000000),(17050149618987/100000000000000),(49088722509/100000000000000),(62813463/100000000000000)⟩
def e91 : ℝ := (30321/100000000000000)
theorem h91 : Model (fun x => f91 ((81/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(63931571136116087/10000000000000),(189173274882719/2000000000000),(28581621052423/50000000000000),(180825405541/100000000000000)⟩
def e92 : ℝ := (158371589/50000000000000)
theorem h92 : Model (fun x => f92 ((81/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(15641724147/100000000000000),(-231419011/100000000000000),(2025263/100000000000000),(-107/781250000000)⟩
def e93 : ℝ := (99/100000000000000)
theorem h93 : Model (fun x => f93 ((81/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (125959940646554271/20000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(630862984621/4000000000000),(355871888191/100000000000000),(-633224563/100000000000000),(1502261/100000000000000)⟩
def e94 : ℝ := (13217/4000000000000)
theorem h94 : Model (fun x => f94 ((81/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(26833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((81/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(42704626334519/100000000000000),(-75986879599/50000000000000),(540831883/100000000000000),(-1924669/100000000000000)⟩
def e96 : ℝ := (6877/100000000000000)
theorem h96 : Model (fun x => f96 ((81/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (233333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(114590747330957/100000000000000),(303947518393/100000000000000),(-135207971/12500000000000),(481167/12500000000000)⟩
def e97 : ℝ := (50653/100000000000000)
theorem h97 : Model (fun x => f97 ((81/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2406405693950097/100000000000000),(6382897886253/100000000000000),(-2839367391/12500000000000),(10104507/12500000000000)⟩
def e98 : ℝ := (1063713/100000000000000)
theorem h98 : Model (fun x => f98 ((81/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(14590747330957/100000000000000),(303947518393/100000000000000),(-135207971/12500000000000),(481167/12500000000000)⟩
def e99 : ℝ := (50653/100000000000000)
theorem h99 : Model (fun x => f99 ((81/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(351112574562021/100000000000000),(1649104578441/20000000000000),(-9942838151/100000000000000),(-33657763/100000000000000)⟩
def e100 : ℝ := (1059731/50000000000000)
theorem h100 : Model (fun x => f100 ((81/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(8206899608667/6250000000000),(17414786641/2500000000000),(-388783063/25000000000000),(449317/20000000000000)⟩
def e101 : ℝ := (75791/50000000000000)
theorem h101 : Model (fun x => f101 ((81/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(114590747330957/10000000000000),(303947518393/10000000000000),(-135207971/1250000000000),(481167/1250000000000)⟩
def e102 : ℝ := (50653/10000000000000)
theorem h102 : Model (fun x => f102 ((81/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(638608933524121/50000000000000),(373606664957/10000000000000),(-3092942483/25000000000000),(8147989/20000000000000)⟩
def e103 : ℝ := (10283/1562500000000)
theorem h103 : Model (fun x => f103 ((81/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(688608933524121/50000000000000),(373606664957/10000000000000),(-3092942483/25000000000000),(8147989/20000000000000)⟩
def e104 : ℝ := (10283/1562500000000)
theorem h104 : Model (fun x => f104 ((81/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(4835585110321233/100000000000000),(63338307151829/50000000000000),(127684847423/100000000000000),(-1712085839/100000000000000)⟩
def e105 : ℝ := (17483041/50000000000000)
theorem h105 : Model (fun x => f105 ((81/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(214590747330957/100000000000000),(303947518393/100000000000000),(-135207971/12500000000000),(481167/12500000000000)⟩
def e106 : ℝ := (50653/100000000000000)
theorem h106 : Model (fun x => f106 ((81/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(230245944200293/50000000000000),(652243251213/50000000000000),(-929614947/25000000000000),(9945257/100000000000000)⟩
def e107 : ℝ := (31611/12500000000000)
theorem h107 : Model (fun x => f107 ((81/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(988172984717253/100000000000000),(2099480500791/50000000000000),(-281109069/3125000000000),(13655157/100000000000000)⟩
def e108 : ℝ := (449139/50000000000000)
theorem h108 : Model (fun x => f108 ((81/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(47783945713204399/100000000000000),(727414206741957/50000000000000),(768233026931/12500000000000),(-4458361697/20000000000000)⟩
def e109 : ℝ := (114455573/25000000000000)
theorem h109 : Model (fun x => f109 ((81/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(172344891782007/781250000000),(365710519461/312500000000),(-8164444323/3125000000000),(9435657/2500000000000)⟩
def e110 : ℝ := (1591611/6250000000000)
theorem h110 : Model (fun x => f110 ((81/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(3218740185308661/100000000000000),(4206321704267/5000000000000),(9870632161/12500000000000),(-1155704187/100000000000000)⟩
def e111 : ℝ := (2939869/12500000000000)
theorem h111 : Model (fun x => f111 ((81/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(6361344191891647/20000000000000),(193293667952131/20000000000000),(4023206064561/100000000000000),(-7616352857/50000000000000)⟩
def e112 : ℝ := (153662707/50000000000000)
theorem h112 : Model (fun x => f112 ((81/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(39795333336331317/50000000000000),(2421296753244569/100000000000000),(10169070280009/100000000000000),(-37524514199/100000000000000)⟩
def e113 : ℝ := (382573853/50000000000000)
theorem h113 : Model (fun x => f113 ((81/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(57448297260669/781250000000),(121903506487/312500000000),(-2721481441/3125000000000),(3145219/2500000000000)⟩
def e114 : ℝ := (530537/6250000000000)
theorem h114 : Model (fun x => f114 ((81/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(1064449538379/50000000000000),(44348214427/50000000000000),(152048821/25000000000000),(-5452087/100000000000000)⟩
def e115 : ℝ := (12569/25000000000000)
theorem h115 : Model (fun x => f115 ((81/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(15531114261/5000000000000),(9706103869/50000000000000),(335303301/100000000000000),(35129/20000000000000)⟩
def e116 : ℝ := (14217/50000000000000)
theorem h116 : Model (fun x => f116 ((81/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(2855155420337/12500000000000),(1548624825627/100000000000000),(31958151669/100000000000000),(127199923/100000000000000)⟩
def e117 : ℝ := (2329361/100000000000000)
theorem h117 : Model (fun x => f117 ((81/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(49015194831691/100000000000000),(848157744759/25000000000000),(18259794443/25000000000000),(88555899/25000000000000)⟩
def e118 : ℝ := (639847/12500000000000)
theorem h118 : Model (fun x => f118 ((81/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(3185587274699773/4000000000000),(484937876844721/20000000000000),(10242109457781/100000000000000),(-37170290603/100000000000000)⟩
def e119 : ℝ := (385133241/50000000000000)
theorem h119 : Model (fun x => f119 ((81/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(4532211279/10000000000000),(3776514909/100000000000000),(26141573/25000000000000),(211689/25000000000000)⟩
def e120 : ℝ := (3381/50000000000000)
theorem h120 : Model (fun x => f120 ((81/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(3306417481/50000000000000),(137755437/20000000000000),(26245393/100000000000000),(40227/10000000000000)⟩
def e121 : ℝ := (657/25000000000000)
theorem h121 : Model (fun x => f121 ((81/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(24121551/2500000000000),(60298643/50000000000000),(5851391/100000000000000),(13127/10000000000000)⟩
def e122 : ℝ := (1367/100000000000000)
theorem h122 : Model (fun x => f122 ((81/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(70390291/50000000000000),(20528719/100000000000000),(1209877/100000000000000),(35671/100000000000000)⟩
def e123 : ℝ := (137/25000000000000)
theorem h123 : Model (fun x => f123 ((81/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(211170873/50000000000000),(61586157/100000000000000),(3629631/100000000000000),(107013/100000000000000)⟩
def e124 : ℝ := (411/25000000000000)
theorem h124 : Model (fun x => f124 ((81/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-211170873/50000000000000),(-61586157/100000000000000),(-3629631/100000000000000),(-107013/100000000000000)⟩
def e125 : ℝ := (411/25000000000000)
theorem h125 : Model (fun x => f125 ((81/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(79639681445152579/100000000000000),(303086165329681/12500000000000),(204842116563/2000000000000),(-2323149851/6250000000000)⟩
def e126 : ℝ := (385134063/50000000000000)
theorem h126 : Model (fun x => f126 ((81/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(172344891782007/625000000000),(365710519461/250000000000),(-8164444323/2500000000000),(9435657/2000000000000)⟩
def e127 : ℝ := (1591611/5000000000000)
theorem h127 : Model (fun x => f127 ((81/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(132532987051711/6250000000000),(3003527264477/25000000000000),(-8614780521/50000000000000),(-338713/6250000000000)⟩
def e128 : ℝ := (2733967/100000000000000)
theorem h128 : Model (fun x => f128 ((81/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(584739412760915641/100000000000000),(1603727450823341/25000000000000),(5898488884573/100000000000000),(-55929661873/100000000000000)⟩
def e129 : ℝ := (385457479/25000000000000)
theorem h129 : Model (fun x => f129 ((81/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(17101634987/100000000000000),(-750457/400000000000),(1885719/100000000000000),(-429/2500000000000)⟩
def e130 : ℝ := (203/100000000000000)
theorem h130 : Model (fun x => f130 ((81/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (115663709399449183/20000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(13619687625559/100000000000000),(3315576581/1250000000000),(-129571453/10000000000000),(3242131/50000000000000)⟩
def e131 : ℝ := (45547/10000000000000)
theorem h131 : Model (fun x => f131 ((81/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(7347815560271/25000000000000),(621118014671/100000000000000),(-1928939093/100000000000000),(7986523/100000000000000)⟩
def e132 : ℝ := (157179/20000000000000)
theorem h132 : Model (fun x => f132 ((81/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-153120010516559/50000000000000),(-1284195676539/20000000000000),(518593057/2500000000000),(-91969571/100000000000000)⟩
def e133 : ℝ := (23223767/100000000000000)
theorem h133 : Model (fun x => f133 ((81/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(24691358024691/50000000000000),(-38103947569/6250000000000),(1881676423/25000000000000),(-92922293/100000000000000)⟩
def e134 : ℝ := (290383/25000000000000)
theorem h134 : Model (fun x => f134 ((81/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := 2)
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-151229640016353/100000000000000),(-1303820929523/100000000000000),(26340368159/100000000000000),(-370606801/100000000000000)⟩
def e135 : ℝ := (5839653/25000000000000)
theorem h135 : Model (fun x => f135 ((81/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(43046721/256000),(531441/64000),(19683/128000),(81/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((81/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((81/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(4782969/32000),(177147/32000),(2187/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((81/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(81310473/256000),(177147/12800),(28431/128000),(99/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((81/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-6561/1600),(-81/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((81/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(80260713/256000),(175851/12800),(28351/128000),(99/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((81/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((81/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(243/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((81/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-243/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((81/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(77150313/256000),(173931/12800),(28351/128000),(99/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((81/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(77918313/256000),(173931/12800),(28351/128000),(99/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((81/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((81/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(77918313/4000),(173931/200),(28351/2000),(99/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((81/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((81/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(8135830269/512000),(100442349/128000),(3720087/256000),(15309/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((81/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(393321873/6250000000000),(-155386419/50000000000000),(4795877/50000000000000),(-118417/50000000000000)⟩
def e151 : ℝ := (5859/100000000000000)
theorem h151 : Model (fun x => f151 ((81/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (3863279637/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(383087210127/312500000000),(-4646835843/800000000000),(2893358769/50000000000000),(-54248129/100000000000000)⟩
def e152 : ℝ := (224156811/100000000000000)
theorem h152 : Model (fun x => f152 ((81/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(201/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((81/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(32361/1600),(181/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((81/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(363/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((81/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(2754820936639/50000000000000),(-22767115179/50000000000000),(376315953/100000000000000),(-62201/2000000000000)⟩
def e156 : ℝ := (25919/100000000000000)
theorem h156 : Model (fun x => f156 ((81/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := 18)
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(55717975206609/50000000000000),(40699775743/12500000000000),(752631899/100000000000000),(-1244023/20000000000000)⟩
def e157 : ℝ := (500253/50000000000000)
theorem h157 : Model (fun x => f157 ((81/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(105717975206609/50000000000000),(40699775743/12500000000000),(752631899/100000000000000),(-1244023/20000000000000)⟩
def e158 : ℝ := (500253/50000000000000)
theorem h158 : Model (fun x => f158 ((81/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(105717975206609/100000000000000),(40699775743/25000000000000),(376315949/100000000000000),(-1555029/50000000000000)⟩
def e159 : ℝ := (250127/50000000000000)
theorem h159 : Model (fun x => f159 ((81/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(5717975206609/100000000000000),(40699775743/25000000000000),(376315949/100000000000000),(-1555029/50000000000000)⟩
def e160 : ℝ := (250127/50000000000000)
theorem h160 : Model (fun x => f160 ((81/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((81/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((81/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(195074835202671/50000000000000),(600806213349/100000000000000),(1388785049/100000000000000),(-2295519/20000000000000)⟩
def e163 : ℝ := (923089/50000000000000)
theorem h163 : Model (fun x => f163 ((81/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2745863956119627/100000000000000),(600806213349/100000000000000),(1388785049/100000000000000),(-2295519/20000000000000)⟩
def e164 : ℝ := (1846179/100000000000000)
theorem h164 : Model (fun x => f164 ((81/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((81/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(18142948602111/625000000000),(2552701026531/50000000000000),(3194856641/25000000000000),(-1453281/1562500000000)⟩
def e166 : ℝ := (1965787/12500000000000)
theorem h166 : Model (fun x => f166 ((81/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(1023156591089839/12500000000000),(2552701026531/50000000000000),(3194856641/25000000000000),(-1453281/1562500000000)⟩
def e167 : ℝ := (15726297/100000000000000)
theorem h167 : Model (fun x => f167 ((81/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((81/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4326641725172567/50000000000000),(18722845694999/100000000000000),(13156027809/25000000000000),(-156438573/50000000000000)⟩
def e169 : ℝ := (11577341/20000000000000)
theorem h169 : Model (fun x => f169 ((81/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13922331069392753/100000000000000),(18722845694999/100000000000000),(13156027809/25000000000000),(-156438573/50000000000000)⟩
def e170 : ℝ := (28943353/50000000000000)
theorem h170 : Model (fun x => f170 ((81/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((81/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(3679601627030663/25000000000000),(21229421731787/50000000000000),(69252860999/50000000000000),(-15190783/2500000000000)⟩
def e172 : ℝ := (65964251/50000000000000)
theorem h172 : Model (fun x => f172 ((81/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(17054120793836937/100000000000000),(21229421731787/50000000000000),(69252860999/50000000000000),(-15190783/2500000000000)⟩
def e173 : ℝ := (131928503/100000000000000)
theorem h173 : Model (fun x => f173 ((81/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((81/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(18029271192533683/100000000000000),(72650585277961/100000000000000),(279725437641/100000000000000),(-384523/48828125000)⟩
def e175 : ℝ := (227009551/100000000000000)
theorem h175 : Model (fun x => f175 ((81/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(3686330428982927/20000000000000),(72650585277961/100000000000000),(279725437641/100000000000000),(-384523/48828125000)⟩
def e176 : ℝ := (14188097/6250000000000)
theorem h176 : Model (fun x => f176 ((81/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((81/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(19485569444729269/100000000000000),(106811292086451/100000000000000),(483355816633/100000000000000),(-338490583/50000000000000)⟩
def e178 : ℝ := (167715407/50000000000000)
theorem h178 : Model (fun x => f178 ((81/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(19467950397110221/100000000000000),(106811292086451/100000000000000),(483355816633/100000000000000),(-338490583/50000000000000)⟩
def e179 : ℝ := (67086163/20000000000000)
theorem h179 : Model (fun x => f179 ((81/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((81/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(20581122974051921/100000000000000),(72306191949671/50000000000000),(151628562013/20000000000000),(-132308469/100000000000000)⟩
def e181 : ℝ := (455706639/100000000000000)
theorem h181 : Model (fun x => f181 ((81/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(10292228153692627/50000000000000),(72306191949671/50000000000000),(151628562013/20000000000000),(-132308469/100000000000000)⟩
def e182 : ℝ := (5696333/1250000000000)
theorem h182 : Model (fun x => f182 ((81/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(1177014108071551/100000000000000),(41780210477137/100000000000000),(44530084223/12500000000000),(1130695263/100000000000000)⟩
def e183 : ℝ := (26477319/20000000000000)
theorem h183 : Model (fun x => f183 ((81/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(111762902817851/100000000000000),(344215830633/100000000000000),(530351341/50000000000000),(-5350503/100000000000000)⟩
def e184 : ℝ := (213617/20000000000000)
theorem h184 : Model (fun x => f184 ((81/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(205717975206609/100000000000000),(40699775743/25000000000000),(376315949/100000000000000),(-1555029/50000000000000)⟩
def e185 : ℝ := (250127/50000000000000)
theorem h185 : Model (fun x => f185 ((81/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(423198853231069/100000000000000),(669814036577/100000000000000),(90666729/5000000000000),(-11570619/100000000000000)⟩
def e186 : ℝ := (2068593/100000000000000)
theorem h186 : Model (fun x => f186 ((81/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(6801532124723/781250000000),(2066891810543/100000000000000),(1282674241/20000000000000),(-3936483/12500000000000)⟩
def e187 : ℝ := (320611/5000000000000)
theorem h187 : Model (fun x => f187 ((81/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(895486346880461/50000000000000),(5669290643147/100000000000000),(19834530733/100000000000000),(-14728303/20000000000000)⟩
def e188 : ℝ := (17658853/100000000000000)
theorem h188 : Model (fun x => f188 ((81/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2001643071222267/100000000000000),(12500975326201/100000000000000),(30339569291/50000000000000),(-4972203/10000000000000)⟩
def e189 : ℝ := (1966759/5000000000000)
theorem h189 : Model (fun x => f189 ((81/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((81/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(105717975206609/12500000000000),(40699775743/3125000000000),(376315949/12500000000000),(-1555029/6250000000000)⟩
def e191 : ℝ := (250127/6250000000000)
theorem h191 : Model (fun x => f191 ((81/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(957506704470723/100000000000000),(1646608654409/100000000000000),(2035615137/50000000000000),(-30230967/100000000000000)⟩
def e192 : ℝ := (5070117/100000000000000)
theorem h192 : Model (fun x => f192 ((81/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1057506704470723/100000000000000),(1646608654409/100000000000000),(2035615137/50000000000000),(-30230967/100000000000000)⟩
def e193 : ℝ := (5070117/100000000000000)
theorem h193 : Model (fun x => f193 ((81/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(10583754838874581/50000000000000),(16515788023993/10000000000000),(929019599019/100000000000000),(188580791/50000000000000)⟩
def e194 : ℝ := (520891907/100000000000000)
theorem h194 : Model (fun x => f194 ((81/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(236211064793/50000000000000),(-921509411/25000000000000),(25081/312500000000),(90737/100000000000000)⟩
def e195 : ℝ := (12817/100000000000000)
theorem h195 : Model (fun x => f195 ((81/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (5250355469964181/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(5560475114879/100000000000000),(76996888491/50000000000000),(118695851/50000000000000),(-1684139/50000000000000)⟩
def e196 : ℝ := (162363/20000000000000)
theorem h196 : Model (fun x => f196 ((81/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(55717975206609/25000000000000),(40699775743/6250000000000),(752631899/50000000000000),(-1244023/10000000000000)⟩
def e197 : ℝ := (500253/25000000000000)
theorem h197 : Model (fun x => f197 ((81/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(47295646650707/100000000000000),(-72832352627/100000000000000),(-28098649/50000000000000),(1737159/100000000000000)⟩
def e198 : ℝ := (28641/12500000000000)
theorem h198 : Model (fun x => f198 ((81/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (105554796177377/50000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(21081741339717/20000000000000),(36416176313/25000000000000),(112394593/100000000000000),(-1737161/50000000000000)⟩
def e199 : ℝ := (147957/10000000000000)
theorem h199 : Model (fun x => f199 ((81/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(1081741339717/20000000000000),(36416176313/25000000000000),(112394593/100000000000000),(-1737161/50000000000000)⟩
def e200 : ℝ := (147957/10000000000000)
theorem h200 : Model (fun x => f200 ((81/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(24313020146251/6250000000000),(21502885061/4000000000000),(414789569/100000000000000),(-12821903/100000000000000)⟩
def e201 : ℝ := (5460319/100000000000000)
theorem h201 : Model (fun x => f201 ((81/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2744722608054301/100000000000000),(21502885061/4000000000000),(414789569/100000000000000),(-12821903/100000000000000)⟩
def e202 : ℝ := (34127/625000000000)
theorem h202 : Model (fun x => f202 ((81/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(289317660361371/10000000000000),(4564739923149/100000000000000),(2152598489/50000000000000),(-43067/40000000000)⟩
def e203 : ℝ := (9283717/20000000000000)
theorem h203 : Model (fun x => f203 ((81/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4087778777997331/50000000000000),(4564739923149/100000000000000),(2152598489/50000000000000),(-43067/40000000000)⟩
def e204 : ℝ := (23209293/50000000000000)
theorem h204 : Model (fun x => f204 ((81/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8617749485172417/100000000000000),(522516722931/3125000000000),(407523041/2000000000000),(-386134441/100000000000000)⟩
def e205 : ℝ := (170338467/100000000000000)
theorem h205 : Model (fun x => f205 ((81/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(3471699276055009/25000000000000),(522516722931/3125000000000),(407523041/2000000000000),(-386134441/100000000000000)⟩
def e206 : ℝ := (42584617/25000000000000)
theorem h206 : Model (fun x => f206 ((81/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(3659473307353723/25000000000000),(18926530954209/50000000000000),(7680270707/12500000000000),(-841017529/100000000000000)⟩
def e207 : ℝ := (3093073/800000000000)
theorem h207 : Model (fun x => f207 ((81/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(16973607515129177/100000000000000),(18926530954209/50000000000000),(7680270707/12500000000000),(-841017529/100000000000000)⟩
def e208 : ℝ := (193317063/50000000000000)
theorem h208 : Model (fun x => f208 ((81/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(3578332032358299/20000000000000),(32312489180511/50000000000000),(138981360327/100000000000000),(-1344179137/100000000000000)⟩
def e209 : ℝ := (662281321/100000000000000)
theorem h209 : Model (fun x => f209 ((81/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(18294041114172447/100000000000000),(32312489180511/50000000000000),(138981360327/100000000000000),(-1344179137/100000000000000)⟩
def e210 : ℝ := (331140661/50000000000000)
theorem h210 : Model (fun x => f210 ((81/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(9641756070678293/50000000000000),(11846039370279/12500000000000),(10447830071/4000000000000),(-1777393969/100000000000000)⟩
def e211 : ℝ := (97475251/10000000000000)
theorem h211 : Model (fun x => f211 ((81/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(9632946546868769/50000000000000),(11846039370279/12500000000000),(10447830071/4000000000000),(-1777393969/100000000000000)⟩
def e212 : ℝ := (974752511/100000000000000)
theorem h212 : Model (fun x => f212 ((81/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(4061585748808149/20000000000000),(15994707693861/12500000000000),(43502087269/10000000000000),(-82236107/4000000000000)⟩
def e213 : ℝ := (1320952617/100000000000000)
theorem h213 : Model (fun x => f213 ((81/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(10155631038687039/50000000000000),(15994707693861/12500000000000),(43502087269/10000000000000),(-82236107/4000000000000)⟩
def e214 : ℝ := (660476309/50000000000000)
theorem h214 : Model (fun x => f214 ((81/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(549288296273043/50000000000000),(36507194649623/100000000000000),(232746913971/100000000000000),(-9846757/25000000000000)⟩
def e215 : ℝ := (19138007/5000000000000)
theorem h215 : Model (fun x => f215 ((81/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(111109954478683/100000000000000),(76771640961/25000000000000),(449129437/100000000000000),(-3498519/50000000000000)⟩
def e216 : ℝ := (3133511/100000000000000)
theorem h216 : Model (fun x => f216 ((81/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(41081741339717/20000000000000),(36416176313/25000000000000),(112394593/100000000000000),(-1737161/50000000000000)⟩
def e217 : ℝ := (147957/10000000000000)
theorem h217 : Model (fun x => f217 ((81/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(421927367875853/100000000000000),(149603993587/25000000000000),(673918623/100000000000000),(-6972841/50000000000000)⟩
def e218 : ℝ := (6092651/100000000000000)
theorem h218 : Model (fun x => f218 ((81/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(86667554956117/10000000000000),(1843797770379/100000000000000),(136509597/5000000000000),(-2603157/6250000000000)⟩
def e219 : ℝ := (18815683/100000000000000)
theorem h219 : Model (fun x => f219 ((81/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1780227037626453/100000000000000),(631220192379/12500000000000),(4633955499/50000000000000),(-109615623/100000000000000)⟩
def e220 : ℝ := (1291217/2500000000000)
theorem h220 : Model (fun x => f220 ((81/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(989004725561979/50000000000000),(11077625785769/100000000000000),(16900117277/50000000000000),(-195216557/100000000000000)⟩
def e221 : ℝ := (114137283/100000000000000)
theorem h221 : Model (fun x => f221 ((81/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(21081741339717/2500000000000),(36416176313/3125000000000),(112394593/12500000000000),(-1737161/6250000000000)⟩
def e222 : ℝ := (147957/1250000000000)
theorem h222 : Model (fun x => f222 ((81/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(954379608067363/100000000000000),(73620210293/5000000000000),(1348286181/100000000000000),(-17395807/50000000000000)⟩
def e223 : ℝ := (14970071/100000000000000)
theorem h223 : Model (fun x => f223 ((81/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1054379608067363/100000000000000),(73620210293/5000000000000),(1348286181/100000000000000),(-17395807/50000000000000)⟩
def e224 : ℝ := (14970071/100000000000000)
theorem h224 : Model (fun x => f224 ((81/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(10427864149148093/50000000000000),(145924521693817/100000000000000),(546159436683/100000000000000),(-2099470809/100000000000000)⟩
def e225 : ℝ := (47161951/3125000000000)
theorem h225 : Model (fun x => f225 ((81/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(119871143517/25000000000000),(-1677442191/50000000000000),(5458569/50000000000000),(29869/50000000000000)⟩
def e226 : ℝ := (453/1250000000000)
theorem h226 : Model (fun x => f226 ((81/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (4141850801702489/20000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(263375264779/5000000000000),(69095196121/50000000000000),(22289/200000000000),(-3355437/100000000000000)⟩
def e227 : ℝ := (1154137/50000000000000)
theorem h227 : Model (fun x => f227 ((81/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(10827980410459/100000000000000),(36523021153/12500000000000),(124268101/50000000000000),(-1344743/20000000000000)⟩
def e228 : ℝ := (3120089/100000000000000)
theorem h228 : Model (fun x => f228 ((81/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(1659224322701/12500000000000),(295287648991/100000000000000),(-191476217/25000000000000),(6739/500000000000)⟩
def e229 : ℝ := (1443797/5000000000000)
theorem h229 : Model (fun x => f229 ((81/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(6554960287213/100000000000000),(12979125117/20000000000000),(-117940519/10000000000000),(7613069/50000000000000)⟩
def e230 : ℝ := (7468329/50000000000000)
theorem h230 : Model (fun x => f230 ((81/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-7233733986457/5000000000000),(-619462651969/50000000000000),(25160962969/100000000000000),(-355380663/100000000000000)⟩
def e231 : ℝ := (3829527/10000000000000)
theorem h231 : Model (fun x => f231 ((81/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((81/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-6561/320),(-81/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((81/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1701/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((81/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(7047/320),(3/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((81/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((81/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15367/320),(3/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((81/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((81/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(384175/32),(75/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((81/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(12879/1600),(39/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((81/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(22479/1600),(39/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((81/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((81/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4248531/1600),(7371/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((81/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(18830037959/50000000000000),(-26135379/20000000000000),(2128781/100000000000000),(-33/250000000000)⟩
def e244 : ℝ := (71/50000000000000)
theorem h244 : Model (fun x => f244 ((81/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := 2646)
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(28257929034761/6250000000000),(-348076443351/25000000000000),(-2238734243/50000000000000),(-46402203/100000000000000)⟩
def e245 : ℝ := (3440853/100000000000000)
theorem h245 : Model (fun x => f245 ((81/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(729/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((81/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(64881/1600),(441/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((81/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(98481/1600),(441/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((81/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(25921/1600),(161/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((81/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2552726001/2560000),(13643301/640000),(204203/1280000),(301/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((81/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((81/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(131769/160),(1089/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((81/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(121424614287/100000000000000),(-1003509209/50000000000000),(24880393/100000000000000),(-54833/20000000000000)⟩
def e253 : ℝ := (2901/100000000000000)
theorem h253 : Model (fun x => f253 ((81/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (64791/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(30269899419123/25000000000000),(587172713277/100000000000000),(698035467/50000000000000),(-6073629/100000000000000)⟩
def e254 : ℝ := (146367/2500000000000)
theorem h254 : Model (fun x => f254 ((81/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(55269899419123/25000000000000),(587172713277/100000000000000),(698035467/50000000000000),(-6073629/100000000000000)⟩
def e255 : ℝ := (146367/2500000000000)
theorem h255 : Model (fun x => f255 ((81/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(55269899419123/50000000000000),(146793178319/50000000000000),(698035467/100000000000000),(-607363/20000000000000)⟩
def e256 : ℝ := (2927341/100000000000000)
theorem h256 : Model (fun x => f256 ((81/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(5269899419123/50000000000000),(146793178319/50000000000000),(698035467/100000000000000),(-607363/20000000000000)⟩
def e257 : ℝ := (2927341/100000000000000)
theorem h257 : Model (fun x => f257 ((81/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(203972247856287/50000000000000),(1083473459021/100000000000000),(2576083271/100000000000000),(-5603647/50000000000000)⟩
def e258 : ℝ := (2700821/25000000000000)
theorem h258 : Model (fun x => f258 ((81/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2763658781426859/100000000000000),(1083473459021/100000000000000),(2576083271/100000000000000),(-5603647/50000000000000)⟩
def e259 : ℝ := (2160657/20000000000000)
theorem h259 : Model (fun x => f259 ((81/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(305494285756477/10000000000000),(2327848627091/25000000000000),(12659923/50000000000),(-81189667/100000000000000)⟩
def e260 : ℝ := (5809701/6250000000000)
theorem h260 : Model (fun x => f260 ((81/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4168661904972861/50000000000000),(2327848627091/25000000000000),(12659923/50000000000),(-81189667/100000000000000)⟩
def e261 : ℝ := (92955217/100000000000000)
theorem h261 : Model (fun x => f261 ((81/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2304015242001797/25000000000000),(34770041973313/100000000000000),(22704593583/20000000000000),(-101801773/50000000000000)⟩
def e262 : ℝ := (347707017/100000000000000)
theorem h262 : Model (fun x => f262 ((81/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(14485108587054807/100000000000000),(34770041973313/100000000000000),(22704593583/20000000000000),(-101801773/50000000000000)⟩
def e263 : ℝ := (173853509/50000000000000)
theorem h263 : Model (fun x => f263 ((81/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(16011809893631881/100000000000000),(40480518504533/50000000000000),(32867935517/10000000000000),(-88953731/100000000000000)⟩
def e264 : ℝ := (792279/97656250000)
theorem h264 : Model (fun x => f264 ((81/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(9173762089673083/50000000000000),(40480518504533/50000000000000),(32867935517/10000000000000),(-88953731/100000000000000)⟩
def e265 : ℝ := (811293697/100000000000000)
theorem h265 : Model (fun x => f265 ((81/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(20281316319647797/100000000000000),(143359995218597/100000000000000),(729084282967/100000000000000),(437292427/50000000000000)⟩
def e266 : ℝ := (143910031/10000000000000)
theorem h266 : Model (fun x => f266 ((81/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(20683697272028749/100000000000000),(143359995218597/100000000000000),(729084282967/100000000000000),(437292427/50000000000000)⟩
def e267 : ℝ := (1439100311/100000000000000)
theorem h267 : Model (fun x => f267 ((81/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(11431858678406177/50000000000000),(109597181784069/50000000000000),(1371193229437/100000000000000),(434979289/12500000000000)⟩
def e268 : ℝ := (2208033493/100000000000000)
theorem h268 : Model (fun x => f268 ((81/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(11423049154596653/50000000000000),(109597181784069/50000000000000),(1371193229437/100000000000000),(434979289/12500000000000)⟩
def e269 : ℝ := (1104016747/50000000000000)
theorem h269 : Model (fun x => f269 ((81/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(25254031113370201/100000000000000),(309370036212889/100000000000000),(1159356426241/50000000000000),(136070293/1562500000000)⟩
def e270 : ℝ := (3135642487/100000000000000)
theorem h270 : Model (fun x => f270 ((81/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(12628682223351767/50000000000000),(309370036212889/100000000000000),(1159356426241/50000000000000),(136070293/1562500000000)⟩
def e271 : ℝ := (391955311/12500000000000)
theorem h271 : Model (fun x => f271 ((81/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(2662075404525217/100000000000000),(21351831108901/20000000000000),(664480625001/50000000000000),(9117775979/100000000000000)⟩
def e272 : ℝ := (1120579237/100000000000000)
theorem h272 : Model (fun x => f272 ((81/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(61095235635999/50000000000000),(81132442011/12500000000000),(240514349/10000000000000),(-523021/20000000000000)⟩
def e273 : ℝ := (6501987/100000000000000)
theorem h273 : Model (fun x => f273 ((81/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(105269899419123/50000000000000),(146793178319/50000000000000),(698035467/100000000000000),(-607363/20000000000000)⟩
def e274 : ℝ := (2927341/100000000000000)
theorem h274 : Model (fun x => f274 ((81/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(44327006894849/10000000000000),(309058062341/25000000000000),(475151803/12500000000000),(-1737747/20000000000000)⟩
def e275 : ℝ := (12356669/100000000000000)
theorem h275 : Model (fun x => f275 ((81/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(186651982294861/20000000000000),(3904141336477/100000000000000),(7363330359/50000000000000),(-11965351/100000000000000)⟩
def e276 : ℝ := (9775273/25000000000000)
theorem h276 : Model (fun x => f276 ((81/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(982441770127997/50000000000000),(10959695088239/100000000000000),(2449099667/5000000000000),(8477277/50000000000000)⟩
def e277 : ℝ := (109924277/100000000000000)
theorem h277 : Model (fun x => f277 ((81/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(2400900457784717/100000000000000),(6536241767337/25000000000000),(178244543151/100000000000000),(550851773/100000000000000)⟩
def e278 : ℝ := (264507777/100000000000000)
theorem h278 : Model (fun x => f278 ((81/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(55269899419123/6250000000000),(146793178319/6250000000000),(698035467/12500000000000),(-607363/2500000000000)⟩
def e279 : ℝ := (2927341/12500000000000)
theorem h279 : Model (fun x => f279 ((81/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(503254430988983/50000000000000),(374718798649/12500000000000),(3994713613/50000000000000),(-215277/800000000000)⟩
def e280 : ℝ := (5984143/20000000000000)
theorem h280 : Model (fun x => f280 ((81/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(553254430988983/50000000000000),(374718798649/12500000000000),(3994713613/50000000000000),(-215277/800000000000)⟩
def e281 : ℝ := (5984143/20000000000000)
theorem h281 : Model (fun x => f281 ((81/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(3320772041582181/12500000000000),(36126938040091/10000000000000),(736967678219/25000000000000),(6440654989/50000000000000)⟩
def e282 : ℝ := (230294867/6250000000000)
theorem h282 : Model (fun x => f282 ((81/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(47052311343/12500000000000),(-5118857649/100000000000000),(6960481/25000000000000),(687/10000000000000)⟩
def e283 : ℝ := (54387/100000000000000)
theorem h283 : Model (fun x => f283 ((81/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (6550485628878953/25000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(10020544060181/100000000000000),(66398337891/25000000000000),(278779691/100000000000000),(-3799953/100000000000000)⟩
def e284 : ℝ := (5874371/100000000000000)
theorem h284 : Model (fun x => f284 ((81/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(30269899419123/12500000000000),(587172713277/50000000000000),(698035467/25000000000000),(-6073629/50000000000000)⟩
def e285 : ℝ := (146367/1250000000000)
theorem h285 : Model (fun x => f285 ((81/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(1413518041847/3125000000000),(-7508419887/6250000000000),(16717829/50000000000000),(956239/50000000000000)⟩
def e286 : ℝ := (303219/25000000000000)
theorem h286 : Model (fun x => f286 ((81/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (55122754240993/25000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(10953484532179/10000000000000),(12013471819/5000000000000),(-66871319/100000000000000),(-3824959/100000000000000)⟩
def e287 : ℝ := (8299923/100000000000000)
theorem h287 : Model (fun x => f287 ((81/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(953484532179/10000000000000),(12013471819/5000000000000),(-66871319/100000000000000),(-3824959/100000000000000)⟩
def e288 : ℝ := (8299923/100000000000000)
theorem h288 : Model (fun x => f288 ((81/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(202117869343779/50000000000000),(886708634259/100000000000000),(-246787011/100000000000000),(-14115921/100000000000000)⟩
def e289 : ℝ := (30630671/100000000000000)
theorem h289 : Model (fun x => f289 ((81/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2759950024401843/100000000000000),(886708634259/100000000000000),(-246787011/100000000000000),(-14115921/100000000000000)⟩
def e290 : ℝ := (1914417/6250000000000)
theorem h290 : Model (fun x => f290 ((81/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(11809011680419/390625000000),(760257129899/10000000000000),(7278541/50000000000000),(-122214717/100000000000000)⟩
def e291 : ℝ := (262839913/100000000000000)
theorem h291 : Model (fun x => f291 ((81/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(1038185992821027/12500000000000),(760257129899/10000000000000),(7278541/50000000000000),(-122214717/100000000000000)⟩
def e292 : ℝ := (131419957/50000000000000)
theorem h292 : Model (fun x => f292 ((81/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4548701685556007/50000000000000),(5656602756209/20000000000000),(12728610951/100000000000000),(-228299087/50000000000000)⟩
def e293 : ℝ := (195819537/20000000000000)
theorem h293 : Model (fun x => f293 ((81/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14366450990159633/100000000000000),(5656602756209/20000000000000),(12728610951/100000000000000),(-228299087/50000000000000)⟩
def e294 : ℝ := (489548843/50000000000000)
theorem h294 : Model (fun x => f294 ((81/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(15736269870302121/100000000000000),(65497946219273/100000000000000),(72290666849/100000000000000),(-1037975227/100000000000000)⟩
def e295 : ℝ := (567936727/25000000000000)
theorem h295 : Model (fun x => f295 ((81/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(9035992078008203/50000000000000),(65497946219273/100000000000000),(72290666849/100000000000000),(-1037975227/100000000000000)⟩
def e296 : ℝ := (2271746909/100000000000000)
theorem h296 : Model (fun x => f296 ((81/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(9897559945935483/50000000000000),(115164528554573/100000000000000),(112235021081/50000000000000),(-1698297507/100000000000000)⟩
def e297 : ℝ := (4004267367/100000000000000)
theorem h297 : Model (fun x => f297 ((81/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(10098750422125959/50000000000000),(115164528554573/100000000000000),(112235021081/50000000000000),(-1698297507/100000000000000)⟩
def e298 : ℝ := (500533421/12500000000000)
theorem h298 : Model (fun x => f298 ((81/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(22123301308618567/100000000000000),(3493474193183/2000000000000),(127267935481/25000000000000),(-271306601/12500000000000)⟩
def e299 : ℝ := (6090289727/100000000000000)
theorem h299 : Model (fun x => f299 ((81/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(22105682260999519/100000000000000),(3493474193183/2000000000000),(127267935481/25000000000000),(-271306601/12500000000000)⟩
def e300 : ℝ := (95160777/1562500000000)
theorem h300 : Model (fun x => f300 ((81/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(24213424871912193/100000000000000),(244441775869439/100000000000000),(962516121493/100000000000000),(-1058299109/50000000000000)⟩
def e301 : ℝ := (8547176833/100000000000000)
theorem h301 : Model (fun x => f301 ((81/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(12108379102622763/50000000000000),(244441775869439/100000000000000),(962516121493/100000000000000),(-1058299109/50000000000000)⟩
def e302 : ℝ := (4273588417/50000000000000)
theorem h302 : Model (fun x => f302 ((81/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(2309030436822049/100000000000000),(40746306840119/50000000000000),(662899234909/100000000000000),(1021075181/100000000000000)⟩
def e303 : ℝ := (288095839/10000000000000)
theorem h303 : Model (fun x => f303 ((81/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(29994705849171/25000000000000),(131589377747/25000000000000),(107699807/25000000000000),(-8700669/100000000000000)⟩
def e304 : ℝ := (18240857/100000000000000)
theorem h304 : Model (fun x => f304 ((81/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(20953484532179/10000000000000),(12013471819/5000000000000),(-66871319/100000000000000),(-3824959/100000000000000)⟩
def e305 : ℝ := (8299923/100000000000000)
theorem h305 : Model (fun x => f305 ((81/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(54881064255033/12500000000000),(251724095937/25000000000000),(29705659/10000000000000),(-16350587/100000000000000)⟩
def e306 : ℝ := (34840703/100000000000000)
theorem h306 : Model (fun x => f306 ((81/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(229989906195471/25000000000000),(791174542589/25000000000000),(13740519/500000000000),(-6376649/12500000000000)⟩
def e307 : ℝ := (109689439/100000000000000)
theorem h307 : Model (fun x => f307 ((81/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(48190899420241/2500000000000),(8841527221543/100000000000000),(796678023/6250000000000),(-68795957/50000000000000)⟩
def e308 : ℝ := (76741401/25000000000000)
theorem h308 : Model (fun x => f308 ((81/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1156377482173691/50000000000000),(20754217079149/100000000000000),(14027160443/20000000000000),(-227615161/100000000000000)⟩
def e309 : ℝ := (181145901/25000000000000)
theorem h309 : Model (fun x => f309 ((81/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(10953484532179/1250000000000),(12013471819/625000000000),(-66871319/12500000000000),(-3824959/12500000000000)⟩
def e310 : ℝ := (8299923/12500000000000)
theorem h310 : Model (fun x => f310 ((81/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(249064396492751/25000000000000),(612128250507/25000000000000),(-26042831/25000000000000),(-39300341/100000000000000)⟩
def e311 : ℝ := (84640241/100000000000000)
theorem h311 : Model (fun x => f311 ((81/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(274064396492751/25000000000000),(612128250507/25000000000000),(-26042831/25000000000000),(-39300341/100000000000000)⟩
def e312 : ℝ := (84640241/100000000000000)
theorem h312 : Model (fun x => f312 ((81/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(6338437935394791/25000000000000),(142073892573077/50000000000000),(9958043191/781250000000),(-427126191/25000000000000)⟩
def e313 : ℝ := (9950023397/100000000000000)
theorem h313 : Model (fun x => f313 ((81/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(394418944459/100000000000000),(-2210191033/50000000000000),(14855863/50000000000000),(-42091/50000000000000)⟩
def e314 : ℝ := (31837/20000000000000)
theorem h314 : Model (fun x => f314 ((81/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (25068317668376401/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(182145069523/2000000000000),(219354339361/100000000000000),(-301631919/100000000000000),(-3006291/100000000000000)⟩
def e315 : ℝ := (3845287/25000000000000)
theorem h315 : Model (fun x => f315 ((81/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(19127797536331/100000000000000),(19397907637/4000000000000),(-5713057/25000000000000),(-1701561/25000000000000)⟩
def e316 : ℝ := (21255519/100000000000000)
theorem h316 : Model (fun x => f316 ((81/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(43240955629833/50000000000000),(1926261360293/100000000000000),(-1927929217/25000000000000),(-12208757/20000000000000)⟩
def e317 : ℝ := (12150403/12500000000000)
theorem h317 : Model (fun x => f317 ((81/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(42707116671439/100000000000000),(423991823953/100000000000000),(-9042722207/100000000000000),(40746733/50000000000000)⟩
def e318 : ℝ := (2065177/4000000000000)
theorem h318 : Model (fun x => f318 ((81/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-101967563057701/100000000000000),(-162986695997/20000000000000),(8059120381/50000000000000),(-273887197/100000000000000)⟩
def e319 : ℝ := (17984939/20000000000000)
theorem h319 : Model (fun x => f319 ((81/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((81/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-72171/1600),(-891/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((81/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((81/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(7857/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((81/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(242109/1600),(1049/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((81/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((81/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(414909/1600),(1049/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((81/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2074545/32),(5245/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((81/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((81/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1028405613052893511/100000000000000),(713694006122387/20000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (26647/20000000000000)
theorem h329 : Model (fun x => f329 ((81/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9723789789/100000000000000),(-3374063/10000000000000),(34353/6250000000000),(-3409/100000000000000)⟩
def e330 : ℝ := (1/2500000000000)
theorem h330 : Model (fun x => f330 ((81/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (16012365521974551/1562500000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(315194366997203/50000000000000),(500095306613/50000000000000),(393002911/5000000000000),(429233/2500000000000)⟩
def e331 : ℝ := (934889/20000000000000)
theorem h331 : Model (fun x => f331 ((81/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((81/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(441/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((81/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((81/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((81/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(655806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((81/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((81/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((81/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2909480792986139/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (211/20000000000000)
theorem h339 : Model (fun x => f339 ((81/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3754193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((81/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((81/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((81/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1057759603506801/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (527/50000000000000)
theorem h343 : Model (fun x => f343 ((81/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(590871496631/12500000000000),(-6295589421/100000000000000),(8384743/100000000000000),(-349/3125000000000)⟩
def e344 : ℝ := (1/5000000000000)
theorem h344 : Model (fun x => f344 ((81/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2112701665378067/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(137530341645669/100000000000000),(865389624861/100000000000000),(-72035251/6250000000000),(1535011/100000000000000)⟩
def e345 : ℝ := (3117/100000000000000)
theorem h345 : Model (fun x => f345 ((81/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(237530341645669/100000000000000),(865389624861/100000000000000),(-72035251/6250000000000),(1535011/100000000000000)⟩
def e346 : ℝ := (3117/100000000000000)
theorem h346 : Model (fun x => f346 ((81/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(59382585411417/50000000000000),(43269481243/10000000000000),(-72035251/12500000000000),(153501/20000000000000)⟩
def e347 : ℝ := (39/2500000000000)
theorem h347 : Model (fun x => f347 ((81/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(9382585411417/50000000000000),(43269481243/10000000000000),(-72035251/12500000000000),(153501/20000000000000)⟩
def e348 : ℝ := (39/2500000000000)
theorem h348 : Model (fun x => f348 ((81/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(219150017589753/50000000000000),(319369980603/20000000000000),(-212675503/10000000000000),(1416229/50000000000000)⟩
def e349 : ℝ := (9/156250000000)
theorem h349 : Model (fun x => f349 ((81/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2794014320893791/100000000000000),(319369980603/20000000000000),(-212675503/10000000000000),(1416229/50000000000000)⟩
def e350 : ℝ := (5761/100000000000000)
theorem h350 : Model (fun x => f350 ((81/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(829578970255989/25000000000000),(6993028270079/50000000000000),(-1464719923/12500000000000),(1280691/20000000000000)⟩
def e351 : ℝ := (87281/100000000000000)
theorem h351 : Model (fun x => f351 ((81/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(2150174208351227/25000000000000),(6993028270079/50000000000000),(-1464719923/12500000000000),(1280691/20000000000000)⟩
def e352 : ℝ := (43641/50000000000000)
theorem h352 : Model (fun x => f352 ((81/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(10214632286147413/100000000000000),(53825332972271/100000000000000),(-11855777/400000000000),(-14421353/25000000000000)⟩
def e353 : ℝ := (88227/20000000000000)
theorem h353 : Model (fun x => f353 ((81/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(1935459988149379/12500000000000),(53825332972271/100000000000000),(-11855777/400000000000),(-14421353/25000000000000)⟩
def e354 : ℝ := (27571/6250000000000)
theorem h354 : Model (fun x => f354 ((81/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(18389218889065701/100000000000000),(65461414186761/50000000000000),(70074814311/50000000000000),(-17042669/6250000000000)⟩
def e355 : ℝ := (237279/25000000000000)
theorem h355 : Model (fun x => f355 ((81/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(10362466587389993/50000000000000),(65461414186761/50000000000000),(70074814311/50000000000000),(-17042669/6250000000000)⟩
def e356 : ℝ := (949117/100000000000000)
theorem h356 : Model (fun x => f356 ((81/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(6153500571986411/25000000000000),(61291607872689/25000000000000),(613511171443/100000000000000),(-312851713/100000000000000)⟩
def e357 : ℝ := (2442039/100000000000000)
theorem h357 : Model (fun x => f357 ((81/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(6254095810081649/25000000000000),(61291607872689/25000000000000),(613511171443/100000000000000),(-312851713/100000000000000)⟩
def e358 : ℝ := (61051/2500000000000)
theorem h358 : Model (fun x => f358 ((81/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(29710750289068697/100000000000000),(399416923698743/100000000000000),(329059021199/20000000000000),(531112049/50000000000000)⟩
def e359 : ℝ := (6319063/100000000000000)
theorem h359 : Model (fun x => f359 ((81/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(29693131241449649/100000000000000),(399416923698743/100000000000000),(329059021199/20000000000000),(531112049/50000000000000)⟩
def e360 : ℝ := (789883/12500000000000)
theorem h360 : Model (fun x => f360 ((81/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(7053019608311193/20000000000000),(18839025945497/3125000000000),(351117767903/10000000000000),(1576696809/25000000000000)⟩
def e361 : ℝ := (9828019/100000000000000)
theorem h361 : Model (fun x => f361 ((81/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(17634215687444649/50000000000000),(18839025945497/3125000000000),(351117767903/10000000000000),(1576696809/25000000000000)⟩
def e362 : ℝ := (491401/5000000000000)
theorem h362 : Model (fun x => f362 ((81/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(3309090697015979/50000000000000),(265730285785557/100000000000000),(1532064240079/50000000000000),(131727407/1000000000000)⟩
def e363 : ℝ := (1767209/12500000000000)
theorem h363 : Model (fun x => f363 ((81/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(141051658005769/100000000000000),(128472683281/12500000000000),(62925423/12500000000000),(-791007/25000000000000)⟩
def e364 : ℝ := (13693/100000000000000)
theorem h364 : Model (fun x => f364 ((81/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(109382585411417/50000000000000),(43269481243/10000000000000),(-72035251/12500000000000),(153501/20000000000000)⟩
def e365 : ℝ := (39/2500000000000)
theorem h365 : Model (fun x => f365 ((81/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(478581999651437/100000000000000),(473292772777/25000000000000),(-81145079/12500000000000),(-814509/50000000000000)⟩
def e366 : ℝ := (16813/100000000000000)
theorem h366 : Model (fun x => f366 ((81/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1308713411331/125000000000),(3106199228573/50000000000000),(2006766889/50000000000000),(-26581/195312500000)⟩
def e367 : ℝ := (55579/100000000000000)
theorem h367 : Model (fun x => f367 ((81/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(7157522824699/312500000000),(9060376064647/50000000000000),(925857373/3125000000000),(-8034363/20000000000000)⟩
def e368 : ℝ := (86353/50000000000000)
theorem h368 : Model (fun x => f368 ((81/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(807664369310343/25000000000000),(49100003092597/100000000000000),(239561709417/100000000000000),(53318727/20000000000000)⟩
def e369 : ℝ := (1399713/100000000000000)
theorem h369 : Model (fun x => f369 ((81/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(59382585411417/6250000000000),(43269481243/1250000000000),(-72035251/1562500000000),(153501/2500000000000)⟩
def e370 : ℝ := (39/312500000000)
theorem h370 : Model (fun x => f370 ((81/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(1091173024588441/100000000000000),(561167495711/12500000000000),(-102671317/2500000000000),(744003/25000000000000)⟩
def e371 : ℝ := (26173/100000000000000)
theorem h371 : Model (fun x => f371 ((81/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1191173024588441/100000000000000),(561167495711/12500000000000),(-102671317/2500000000000),(744003/25000000000000)⟩
def e372 : ℝ := (26173/100000000000000)
theorem h372 : Model (fun x => f372 ((81/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(1539308815429947/4000000000000),(72990118919139/10000000000000),(2462591089311/50000000000000),(1201001099/10000000000000)⟩
def e373 : ℝ := (2648659/12500000000000)
theorem h373 : Model (fun x => f373 ((81/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(259856889007/100000000000000),(-308043861/6250000000000),(117627/195312500000),(-59259/10000000000000)⟩
def e374 : ℝ := (2689/50000000000000)
theorem h374 : Model (fun x => f374 ((81/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (37747881983178401/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(17197800279371/100000000000000),(72865605977/20000000000000),(-1148903039/100000000000000),(2012983/50000000000000)⟩
def e375 : ℝ := (159339/20000000000000)
theorem h375 : Model (fun x => f375 ((81/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(137530341645669/50000000000000),(865389624861/50000000000000),(-72035251/3125000000000),(1535011/50000000000000)⟩
def e376 : ℝ := (3117/50000000000000)
theorem h376 : Model (fun x => f376 ((81/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(8419976943339/20000000000000),(-153381682481/100000000000000),(190773237/25000000000000),(-1898239/50000000000000)⟩
def e377 : ℝ := (2397/12500000000000)
theorem h377 : Model (fun x => f377 ((81/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (29582974739833/12500000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(57900115283303/50000000000000),(306763364957/100000000000000),(-1526185901/100000000000000),(1518591/20000000000000)⟩
def e378 : ℝ := (71917/50000000000000)
theorem h378 : Model (fun x => f378 ((81/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(7900115283303/50000000000000),(306763364957/100000000000000),(-1526185901/100000000000000),(1518591/20000000000000)⟩
def e379 : ℝ := (71917/50000000000000)
theorem h379 : Model (fun x => f379 ((81/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(26709874609857/6250000000000),(283025723621/25000000000000),(-563235273/10000000000000),(28021619/100000000000000)⟩
def e380 : ℝ := (265409/50000000000000)
theorem h380 : Model (fun x => f380 ((81/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2783072279471997/100000000000000),(283025723621/25000000000000),(-563235273/10000000000000),(28021619/100000000000000)⟩
def e381 : ℝ := (530819/100000000000000)
theorem h381 : Model (fun x => f381 ((81/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3222804116463869/100000000000000),(9848423935757/100000000000000),(-22762128629/50000000000000),(41842107/20000000000000)⟩
def e382 : ℝ := (4879707/100000000000000)
theorem h382 : Model (fun x => f382 ((81/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8505185068844821/100000000000000),(9848423935757/100000000000000),(-22762128629/50000000000000),(41842107/20000000000000)⟩
def e383 : ℝ := (1219927/25000000000000)
theorem h383 : Model (fun x => f383 ((81/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(9849023919838849/100000000000000),(146465974757/390625000000),(-152310773583/100000000000000),(119620831/20000000000000)⟩
def e384 : ℝ := (20004357/100000000000000)
theorem h384 : Model (fun x => f384 ((81/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(3779517884721617/25000000000000),(146465974757/390625000000),(-152310773583/100000000000000),(119620831/20000000000000)⟩
def e385 : ℝ := (10002179/50000000000000)
theorem h385 : Model (fun x => f385 ((81/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(17506761699254969/100000000000000),(44898168352837/50000000000000),(-29208429143/10000000000000),(400516441/50000000000000)⟩
def e386 : ℝ := (10410579/20000000000000)
theorem h386 : Model (fun x => f386 ((81/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(9921237992484627/50000000000000),(44898168352837/50000000000000),(-29208429143/10000000000000),(400516441/50000000000000)⟩
def e387 : ℝ := (1626653/3125000000000)
theorem h387 : Model (fun x => f387 ((81/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(22977632940717821/100000000000000),(41213452991953/25000000000000),(-365605089731/100000000000000),(33552313/20000000000000)⟩
def e388 : ℝ := (102875343/100000000000000)
theorem h388 : Model (fun x => f388 ((81/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(23380013893098773/100000000000000),(41213452991953/25000000000000),(-365605089731/100000000000000),(33552313/20000000000000)⟩
def e389 : ℝ := (6429709/6250000000000)
theorem h389 : Model (fun x => f389 ((81/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(13537054997356447/50000000000000),(262622411702449/100000000000000),(-68620727927/25000000000000),(-1668015899/100000000000000)⟩
def e390 : ℝ := (34391031/20000000000000)
theorem h390 : Model (fun x => f390 ((81/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(13528245473546923/50000000000000),(262622411702449/100000000000000),(-68620727927/25000000000000),(-1668015899/100000000000000)⟩
def e391 : ℝ := (42988789/25000000000000)
theorem h391 : Model (fun x => f391 ((81/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(31331478899967553/100000000000000),(48389595042451/12500000000000),(14969030501/20000000000000),(-590912289/12500000000000)⟩
def e392 : ℝ := (10318679/4000000000000)
theorem h392 : Model (fun x => f392 ((81/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(15667406116650443/50000000000000),(48389595042451/12500000000000),(14969030501/20000000000000),(-590912289/12500000000000)⟩
def e393 : ℝ := (2015367/781250000000)
theorem h393 : Model (fun x => f393 ((81/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(2475486290237301/50000000000000),(31457813021093/20000000000000),(90141327573/12500000000000),(-16184839/400000000000)⟩
def e394 : ℝ := (50504807/50000000000000)
theorem h394 : Model (fun x => f394 ((81/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(134096933992791/100000000000000),(177616341957/25000000000000),(-648403991/25000000000000),(25693/312500000000)⟩
def e395 : ℝ := (202059/50000000000000)
theorem h395 : Model (fun x => f395 ((81/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(107900115283303/50000000000000),(306763364957/100000000000000),(-1526185901/100000000000000),(1518591/20000000000000)⟩
def e396 : ℝ := (71917/50000000000000)
theorem h396 : Model (fun x => f396 ((81/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(465697395126003/100000000000000),(661996048871/50000000000000),(-2822993883/50000000000000),(2340767/10000000000000)⟩
def e397 : ℝ := (345893/50000000000000)
theorem h397 : Model (fun x => f397 ((81/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(62811003276537/6250000000000),(535720874927/12500000000000),(-3807484973/25000000000000),(12086899/25000000000000)⟩
def e398 : ℝ := (2426047/100000000000000)
theorem h398 : Model (fun x => f398 ((81/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(542185159567861/25000000000000),(3082898355429/25000000000000),(-35056885161/100000000000000),(13702591/20000000000000)⟩
def e399 : ℝ := (1480529/20000000000000)
theorem h399 : Model (fun x => f399 ((81/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(727053675544423/25000000000000),(7986109960977/25000000000000),(-3911827751/25000000000000),(-149359391/50000000000000)⟩
def e400 : ℝ := (2651037/12500000000000)
theorem h400 : Model (fun x => f400 ((81/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(57900115283303/6250000000000),(306763364957/12500000000000),(-1526185901/12500000000000),(1518591/2500000000000)⟩
def e401 : ℝ := (71917/6250000000000)
theorem h401 : Model (fun x => f401 ((81/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1060498778525639/100000000000000),(791143071871/25000000000000),(-3700775793/25000000000000),(344827/500000000000)⟩
def e402 : ℝ := (155479/10000000000000)
theorem h402 : Model (fun x => f402 ((81/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1160498778525639/100000000000000),(791143071871/25000000000000),(-3700775793/25000000000000),(344827/500000000000)⟩
def e403 : ℝ := (155479/10000000000000)
theorem h403 : Model (fun x => f403 ((81/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(6749959219135033/20000000000000),(23137369536053/5000000000000),(49851501849/12500000000000),(-668490477/10000000000000)⟩
def e404 : ℝ := (153718617/50000000000000)
theorem h404 : Model (fun x => f404 ((81/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(296298086413/100000000000000),(-2031288811/50000000000000),(52201203/100000000000000),(-304521/50000000000000)⟩
def e405 : ℝ := (9819/100000000000000)
theorem h405 : Model (fun x => f405 ((81/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (33286642900597309/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(7334818507389/50000000000000),(132453692959/50000000000000),(-333765377/20000000000000),(2666987/25000000000000)⟩
def e406 : ℝ := (1228767/100000000000000)
theorem h406 : Model (fun x => f406 ((81/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(31867437294149/100000000000000),(629235415803/100000000000000),(-704432481/25000000000000),(7346957/50000000000000)⟩
def e407 : ℝ := (1012731/50000000000000)
theorem h407 : Model (fun x => f407 ((81/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(200888734515047/100000000000000),(267835268001/6250000000000),(-8964299307/100000000000000),(596879/500000000000)⟩
def e408 : ℝ := (14342077/100000000000000)
theorem h408 : Model (fun x => f408 ((81/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(49602156670381/50000000000000),(445742334443/50000000000000),(-15432798041/100000000000000),(124739691/50000000000000)⟩
def e409 : ℝ := (149563/1000000000000)
theorem h409 : Model (fun x => f409 ((81/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-2763249716939/100000000000000),(76551188901/100000000000000),(685442721/100000000000000),(-4881563/20000000000000)⟩
def e410 : ℝ := (20976199/20000000000000)
theorem h410 : Model (fun x => f410 ((81/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(2543287715332031/50000000000000),(73306680908203/25000000000000),(137781/2048000),(7857/10240000)⟩
def e411 : ℝ := (108886719/25000000000000)
theorem h411 : Model (fun x => f411 ((81/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(40401/1600),(201/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((81/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(8120601/64000),(121203/64000),(603/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((81/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(129081404777581289/20000000000000),(731856793721219/1562500000000),(728431410323089/50000000000000),(3164819893753/12500000000000)⟩
def e414 : ℝ := (135099337247/50000000000000)
theorem h414 : Model (fun x => f414 ((81/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(7747049249/50000000000000),(-1124446269/100000000000000),(46629453/100000000000000),(-1453647/100000000000000)⟩
def e415 : ℝ := (14279/25000000000000)
theorem h415 : Model (fun x => f415 ((81/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (597085737511277733/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(570613127269/10000000000000),(110451969/1562500000000),(-946011383/100000000000000),(10370667/50000000000000)⟩
def e416 : ℝ := (41027021/100000000000000)
theorem h416 : Model (fun x => f416 ((81/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(2942881555751/100000000000000),(83620114917/100000000000000),(-130284331/50000000000000),(-3666481/100000000000000)⟩
def e417 : ℝ := (9119251/6250000000000)
theorem h417 : Model (fun x => f417 ((81/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((81/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((8827946374543/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass 2 (41/20) ∧
    SigmaActualBlockSeparable.endpointCellMass 2 (41/20) ≤ (8828821822639/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(81/40)-(1/40)) (by norm_num : ((81/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel20


noncomputable section
namespace Hf4Quad.Panel21
open Hf4Quad.Dag

def p0 : Cubic := ⟨(83/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((83/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((83/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((83/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((83/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(363619047619047/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((83/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-363619047619047/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((83/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-68047619047619/25000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((83/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((83/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(6889/1600),(83/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((83/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(32576951058201/6250000000000),(3139947089947/25000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((83/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-32576951058201/6250000000000),(-3139947089947/25000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((83/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-198355423280423/25000000000000),(-847037037037/5000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((83/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((83/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(571787/64000),(20667/64000),(249/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((83/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(8704199673032407/100000000000000),(314609626736111/100000000000000),(758095486111/20000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((83/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-8704199673032407/100000000000000),(-314609626736111/100000000000000),(-758095486111/20000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((83/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-9497621366154099/100000000000000),(-331550367476851/100000000000000),(-483267350777/12500000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((83/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((83/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(47458321/2560000),(571787/640000),(20667/1280000),(83/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((83/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(5178983442460317/100000000000000),(249589563492063/100000000000000),(281915922619/6250000000000),(3623015873/10000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((83/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-2159318961846891/50000000000000),(-20490200996197/25000000000000),(80564494461/12500000000000),(4201471561/20000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((83/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((83/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(3846719377929687/100000000000000),(57932520751953/25000000000000),(571787/10240000),(6889/10240000)⟩
def e22 : ℝ := (406250001/100000000000000)
theorem h22 : Model (fun x => f22 ((83/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(25060664391771553/100000000000000),(37741964445439/2500000000000),(9094449263961/25000000000000),(109571677879/25000000000000)⟩
def e23 : ℝ := (2646643527/100000000000000)
theorem h23 : Model (fun x => f23 ((83/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(20742026468077771/100000000000000),(356929443458193/25000000000000),(9255578252883/25000000000000),(459294069321/100000000000000)⟩
def e24 : ℝ := (2755770519/100000000000000)
theorem h24 : Model (fun x => f24 ((83/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((83/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(79819427092041/1000000000000),(144251976672363/25000000000000),(3475951245117/20000000000000),(279192871093/100000000000000)⟩
def e26 : ℝ := (253500977/10000000000000)
theorem h26 : Model (fun x => f26 ((83/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(448086836744209/2500000000000),(323918195236777/25000000000000),(19513144291371/50000000000000),(156732082661/25000000000000)⟩
def e27 : ℝ := (2846185573/50000000000000)
theorem h27 : Model (fun x => f27 ((83/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(38665499937846131/100000000000000),(68084763869497/2500000000000),(38024300797137/50000000000000),(217244479993/20000000000000)⟩
def e28 : ℝ := (1689628333/20000000000000)
theorem h28 : Model (fun x => f28 ((83/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((83/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(16562531121598507/100000000000000),(279367994822143/20000000000000),(2019527673413/4000000000000),(1013819113157/100000000000000)⟩
def e30 : ℝ := (1537917787/12500000000000)
theorem h30 : Model (fun x => f30 ((83/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(122822341402727/3125000000000),(16573617153139/5000000000000),(11980928062509/100000000000000),(60145221197/25000000000000)⟩
def e31 : ℝ := (2919602659/100000000000000)
theorem h31 : Model (fun x => f31 ((83/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(8519162972546679/20000000000000),(152743144892133/5000000000000),(88029529656783/100000000000000),(1326803284753/100000000000000)⟩
def e32 : ℝ := (2841936081/25000000000000)
theorem h32 : Model (fun x => f32 ((83/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((83/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(2955381/320),(35607/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((83/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((83/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(183347/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((83/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(5888933/320),(53279/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((83/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((83/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(6618533/320),(53279/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((83/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-6618533/320),(-53279/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((83/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((83/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(123/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((83/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(15129/1600),(123/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((83/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((83/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(317709/160),(2583/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((83/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(50360550063/100000000000000),(-818870733/100000000000000),(2496557/25000000000000),(-27063/25000000000000)⟩
def e46 : ℝ := (1127/100000000000000)
theorem h46 : Model (fun x => f46 ((83/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (156261/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-520801503890809/50000000000000),(166885860879/100000000000000),(-690043709/50000000000000),(356689/3125000000000)⟩
def e47 : ℝ := (23245511/50000000000000)
theorem h47 : Model (fun x => f47 ((83/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((83/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(163/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((83/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((83/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((83/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(135833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((83/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(235833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((83/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((83/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(23583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((83/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((83/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(495249999999993/20000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((83/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((83/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(3583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((83/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(88732291666657/20000000000000),(11885416666647/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (117/100000000000000)
theorem h60 : Model (fun x => f60 ((83/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(139043402777773/100000000000000),(982638888887/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((83/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((83/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(23583333333333/2000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((83/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1318210069444423/100000000000000),(5149305555547/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((83/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1418210069444423/100000000000000),(5149305555547/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((83/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(6292051476326621/100000000000000),(19140566008359/10000000000000),(1136774631069/100000000000000),(2083695023/100000000000000)⟩
def e66 : ℝ := (79357/12500000000000)
theorem h66 : Model (fun x => f66 ((83/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(43583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((83/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(474876736111103/100000000000000),(1815972222219/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((83/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(103483555410877/10000000000000),(2967979600689/50000000000000),(2837456597/25000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (63/100000000000000)
theorem h69 : Model (fun x => f69 ((83/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(65112385759853631/100000000000000),(2354227431686017/100000000000000),(23839646862887/100000000000000),(111220659533/100000000000000)⟩
def e70 : ℝ := (1068303/390625000000)
theorem h70 : Model (fun x => f70 ((83/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((83/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2919911458333233/12500000000000),(20635416666627/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((83/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(4185206423610577/100000000000000),(126907812499781/100000000000000),(37005208333/5000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1283/100000000000000)
theorem h73 : Model (fun x => f73 ((83/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(866200081687327/2000000000000),(780859655244201/50000000000000),(3133414138089/20000000000000),(4450935849/6250000000000)⟩
def e74 : ℝ := (82763407/50000000000000)
theorem h74 : Model (fun x => f74 ((83/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(108422389844219981/100000000000000),(3915946742174419/100000000000000),(9876679388333/25000000000000),(182435633117/100000000000000)⟩
def e75 : ℝ := (219506191/50000000000000)
theorem h75 : Model (fun x => f75 ((83/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((83/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(973303819444411/12500000000000),(6878472222209/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((83/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(3210069444443/100000000000000),(29861111111/20000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((83/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(575137442129/100000000000000),(8025173611/20000000000000),(466579861/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/50000000000000)
theorem h79 : Model (fun x => f79 ((83/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(44782677530371/100000000000000),(3440858204487/100000000000000),(11912421079/12500000000000),(55788141/5000000000000)⟩
def e80 : ℝ := (611879/12500000000000)
theorem h80 : Model (fun x => f80 ((83/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(48794459059133/50000000000000),(3842398996827/50000000000000),(111005058331/50000000000000),(2828513847/100000000000000)⟩
def e81 : ℝ := (7668251/50000000000000)
theorem h81 : Model (fun x => f81 ((83/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(108519978762338247/100000000000000),(3923631540168073/100000000000000),(19864363834997/50000000000000),(46316036741/25000000000000)⟩
def e82 : ℝ := (113587221/25000000000000)
theorem h82 : Model (fun x => f82 ((83/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(103045458381/100000000000000),(1917124807/20000000000000),(334382233/100000000000000),(259211/5000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((83/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(18462311293/100000000000000),(1073390191/50000000000000),(399401/400000000000),(1161049/50000000000000)⟩
def e84 : ℝ := (2713/10000000000000)
theorem h84 : Model (fun x => f84 ((83/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(3307830773/100000000000000),(230778891/50000000000000),(13417377/50000000000000),(166417/20000000000000)⟩
def e85 : ℝ := (14651/100000000000000)
theorem h85 : Model (fun x => f85 ((83/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(592653013/100000000000000),(96478397/100000000000000),(134621/2000000000000),(260893/100000000000000)⟩
def e86 : ℝ := (1539/25000000000000)
theorem h86 : Model (fun x => f86 ((83/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(1777959039/100000000000000),(289435191/100000000000000),(403863/2000000000000),(782679/100000000000000)⟩
def e87 : ℝ := (4617/25000000000000)
theorem h87 : Model (fun x => f87 ((83/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-1777959039/100000000000000),(-289435191/100000000000000),(-403863/2000000000000),(-782679/100000000000000)⟩
def e88 : ℝ := (4617/25000000000000)
theorem h88 : Model (fun x => f88 ((83/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(13564997123047401/12500000000000),(1961815625366441/50000000000000),(9932176869211/25000000000000),(37052672857/20000000000000)⟩
def e89 : ℝ := (56795919/12500000000000)
theorem h89 : Model (fun x => f89 ((83/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2919911458333233/10000000000000),(20635416666627/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((83/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(140942446562209/6250000000000),(3449451847023/20000000000000),(12366581669/25000000000000),(6305459/10000000000000)⟩
def e91 : ℝ := (15161/50000000000000)
theorem h91 : Model (fun x => f91 ((83/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(658463143492021509/100000000000000),(605593547741599/6250000000000),(29127905094643/50000000000000),(229209801/125000000000)⟩
def e92 : ℝ := (159830287/50000000000000)
theorem h92 : Model (fun x => f92 ((83/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(15186878869/100000000000000),(-55869951/25000000000000),(1944957/100000000000000),(-13079/100000000000000)⟩
def e93 : ℝ := (19/20000000000000)
theorem h93 : Model (fun x => f93 ((83/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (129743041446093053/20000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(4120199363321/25000000000000),(353356893449/100000000000000),(-31215293/5000000000000),(1469697/100000000000000)⟩
def e94 : ℝ := (333/100000000000)
theorem h94 : Model (fun x => f94 ((83/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(135833333333331/50000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((83/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(10600706713781/25000000000000),(-149833310443/100000000000000),(264723163/50000000000000),(-467709/25000000000000)⟩
def e96 : ℝ := (3319/50000000000000)
theorem h96 : Model (fun x => f96 ((83/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (29374999999999/12500000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(115194346289751/100000000000000),(299666620881/100000000000000),(-66180791/6250000000000),(3741667/100000000000000)⟩
def e97 : ℝ := (49333/100000000000000)
theorem h97 : Model (fun x => f97 ((83/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2419081272084771/100000000000000),(6292999038501/100000000000000),(-1389796611/6250000000000),(78575007/100000000000000)⟩
def e98 : ℝ := (1035993/100000000000000)
theorem h98 : Model (fun x => f98 ((83/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(15194346289751/100000000000000),(299666620881/100000000000000),(-66180791/6250000000000),(3741667/100000000000000)⟩
def e99 : ℝ := (49333/100000000000000)
theorem h99 : Model (fun x => f99 ((83/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(367563585511073/100000000000000),(4102679585171/50000000000000),(-10136184519/100000000000000),(-15409643/50000000000000)⟩
def e100 : ℝ := (516277/25000000000000)
theorem h100 : Model (fun x => f100 ((83/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(13269737417123/10000000000000),(86299751243/12500000000000),(-154156811/10000000000000),(2274081/100000000000000)⟩
def e101 : ℝ := (5907/4000000000000)
theorem h101 : Model (fun x => f101 ((83/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(115194346289751/10000000000000),(299666620881/10000000000000),(-66180791/625000000000),(3741667/10000000000000)⟩
def e102 : ℝ := (49333/10000000000000)
theorem h102 : Model (fun x => f102 ((83/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(64232041853437/5000000000000),(1843532109377/50000000000000),(-1213049467/10000000000000),(39690751/100000000000000)⟩
def e103 : ℝ := (128201/20000000000000)
theorem h103 : Model (fun x => f103 ((83/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(69232041853437/5000000000000),(1843532109377/50000000000000),(-1213049467/10000000000000),(39690751/100000000000000)⟩
def e104 : ℝ := (128201/20000000000000)
theorem h104 : Model (fun x => f104 ((83/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1017887101436079/20000000000000),(31791764835817/25000000000000),(117599830669/100000000000000),(-824962981/50000000000000)⟩
def e105 : ℝ := (6885959/20000000000000)
theorem h105 : Model (fun x => f105 ((83/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(215194346289751/100000000000000),(299666620881/100000000000000),(-66180791/6250000000000),(3741667/100000000000000)⟩
def e106 : ℝ := (49333/100000000000000)
theorem h106 : Model (fun x => f106 ((83/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(115771516687683/25000000000000),(644865625853/50000000000000),(-1829676711/50000000000000),(1951483/20000000000000)⟩
def e107 : ℝ := (246341/100000000000000)
theorem h107 : Model (fun x => f107 ((83/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(996535034103157/100000000000000),(2081571552003/50000000000000),(-8913411967/100000000000000),(13701813/100000000000000)⟩
def e108 : ℝ := (438217/50000000000000)
theorem h108 : Model (fun x => f108 ((83/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(5071800786713833/10000000000000),(1479144781544431/100000000000000),(6012427820729/100000000000000),(-22183819957/100000000000000)⟩
def e109 : ℝ := (226086339/50000000000000)
theorem h109 : Model (fun x => f109 ((83/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(278664485759583/1250000000000),(1812294776103/1562500000000),(-3237293031/1250000000000),(47755701/12500000000000)⟩
def e110 : ℝ := (124047/500000000000)
theorem h110 : Model (fun x => f110 ((83/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(423412469528649/12500000000000),(8442860186631/10000000000000),(7216245797/10000000000000),(-1112078233/100000000000000)⟩
def e111 : ℝ := (11570141/50000000000000)
theorem h111 : Model (fun x => f111 ((83/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(8438907195228683/25000000000000),(491189366307359/50000000000000),(3932083709717/100000000000000),(-1513937043/10000000000000)⟩
def e112 : ℝ := (151632479/50000000000000)
theorem h112 : Model (fun x => f112 ((83/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(42236818324026531/50000000000000),(2461523514159149/100000000000000),(4972255765223/50000000000000),(-37323190387/100000000000000)⟩
def e113 : ℝ := (188859409/25000000000000)
theorem h113 : Model (fun x => f113 ((83/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(92888161919861/1250000000000),(604098258701/1562500000000),(-1079097677/1250000000000),(15918567/12500000000000)⟩
def e114 : ℝ := (41349/500000000000)
theorem h114 : Model (fun x => f114 ((83/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(144292599483/6250000000000),(45532384091/50000000000000),(288108601/50000000000000),(-5209253/100000000000000)⟩
def e115 : ℝ := (49009/100000000000000)
theorem h115 : Model (fun x => f115 ((83/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(175394537887/50000000000000),(10377522169/50000000000000),(33599669/10000000000000),(57323/100000000000000)⟩
def e116 : ℝ := (27163/100000000000000)
theorem h116 : Model (fun x => f116 ((83/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(2606732197617/10000000000000),(1677941419999/100000000000000),(16344819273/50000000000000),(5834653/5000000000000)⟩
def e117 : ℝ := (2301623/100000000000000)
theorem h117 : Model (fun x => f117 ((83/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(56095403121863/100000000000000),(3688950132811/100000000000000),(75098459369/100000000000000),(83071139/25000000000000)⟩
def e118 : ℝ := (5039933/100000000000000)
theorem h118 : Model (fun x => f118 ((83/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(3381189282046997/4000000000000),(61630311607299/2500000000000),(2003921997963/20000000000000),(-36990905831/100000000000000)⟩
def e119 : ℝ := (760477569/100000000000000)
theorem h119 : Model (fun x => f119 ((83/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(53300106919/100000000000000),(4204791079/100000000000000),(2738349/2500000000000),(808931/100000000000000)⟩
def e120 : ℝ := (7017/100000000000000)
theorem h120 : Model (fun x => f120 ((83/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(4049301409/50000000000000),(399306573/50000000000000),(28678933/100000000000000),(204309/50000000000000)⟩
def e121 : ℝ := (159/6250000000000)
theorem h121 : Model (fun x => f121 ((83/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(307632439/25000000000000),(18201607/12500000000000),(6664997/100000000000000),(69937/50000000000000)⟩
def e122 : ℝ := (339/25000000000000)
theorem h122 : Model (fun x => f122 ((83/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(23371369/12500000000000),(3226551/12500000000000),(57441/4000000000000),(39729/100000000000000)⟩
def e123 : ℝ := (569/100000000000000)
theorem h123 : Model (fun x => f123 ((83/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(70114107/12500000000000),(9679653/12500000000000),(172323/4000000000000),(119187/100000000000000)⟩
def e124 : ℝ := (1707/100000000000000)
theorem h124 : Model (fun x => f124 ((83/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-70114107/12500000000000),(-9679653/12500000000000),(-172323/4000000000000),(-119187/100000000000000)⟩
def e125 : ℝ := (1707/100000000000000)
theorem h125 : Model (fun x => f125 ((83/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(84529731490262069/100000000000000),(154075774178421/6250000000000),(500980284087/5000000000000),(-18495512509/50000000000000)⟩
def e126 : ℝ := (190119819/25000000000000)
theorem h126 : Model (fun x => f126 ((83/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(278664485759583/1000000000000),(1812294776103/1250000000000),(-3237293031/1000000000000),(47755701/10000000000000)⟩
def e127 : ℝ := (124047/400000000000)
theorem h127 : Model (fun x => f127 ((83/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(428897410437327/20000000000000),(2986282862591/25000000000000),(-17257844643/100000000000000),(-1005297/25000000000000)⟩
def e128 : ℝ := (2674047/100000000000000)
theorem h128 : Model (fun x => f128 ((83/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(298796190807836337/50000000000000),(3218919029312497/50000000000000),(1391749517503/25000000000000),(-27285173097/50000000000000)⟩
def e129 : ℝ := (1524953113/100000000000000)
theorem h129 : Model (fun x => f129 ((83/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(8366907199/50000000000000),(-45068173/25000000000000),(893091/50000000000000),(-4009/25000000000000)⟩
def e130 : ℝ := (47/25000000000000)
theorem h130 : Model (fun x => f130 ((83/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (591148920463678361/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(3536262094677/25000000000000),(130070021417/50000000000000),(-1257587667/100000000000000),(6225369/100000000000000)⟩
def e131 : ℝ := (111039/25000000000000)
theorem h131 : Model (fun x => f131 ((83/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(3828230728999/12500000000000),(613496936283/100000000000000),(-1881893527/100000000000000),(3847533/50000000000000)⟩
def e132 : ℝ := (194289/25000000000000)
theorem h132 : Model (fun x => f132 ((83/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-31899973134459/10000000000000),(-792386541813/12500000000000),(20203035779/100000000000000),(-88263799/100000000000000)⟩
def e133 : ℝ := (22729719/100000000000000)
theorem h133 : Model (fun x => f133 ((83/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(48192771084337/100000000000000),(-580635796197/100000000000000),(3497806001/50000000000000),(-42142241/50000000000000)⟩
def e134 : ℝ := (1027861/100000000000000)
theorem h134 : Model (fun x => f134 ((83/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (41/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-153734810286549/100000000000000),(-601378813817/50000000000000),(1211372927/5000000000000),(-167216931/50000000000000)⟩
def e135 : ℝ := (5430969/25000000000000)
theorem h135 : Model (fun x => f135 ((83/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(47458321/256000),(571787/64000),(20667/128000),(83/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((83/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((83/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(5146083/32000),(186003/32000),(2241/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((83/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(17725397/51200),(943793/64000),(29631/128000),(101/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((83/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-6889/1600),(-83/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((83/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(17504949/51200),(937153/64000),(29551/128000),(101/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((83/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((83/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(249/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((83/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-249/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((83/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(16867509/51200),(927553/64000),(29551/128000),(101/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((83/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(17021109/51200),(927553/64000),(29551/128000),(101/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((83/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((83/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(17021109/800),(927553/1000),(29551/2000),(101/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((83/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((83/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(8969622669/512000),(108067743/128000),(3906063/256000),(15687/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((83/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(5708155391/100000000000000),(-275091827/100000000000000),(4142949/50000000000000),(-199661/100000000000000)⟩
def e151 : ℝ := (4813/100000000000000)
theorem h151 : Model (fun x => f151 ((83/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (4264738317/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(24289783774787/20000000000000),(-279171654041/50000000000000),(2736283423/50000000000000),(-50550603/100000000000000)⟩
def e152 : ℝ := (100561313/50000000000000)
theorem h152 : Model (fun x => f152 ((83/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(203/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((83/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(33089/1600),(183/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((83/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(369/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((83/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(2710027100271/50000000000000),(-22032740653/50000000000000),(71651189/20000000000000),(-58253/2000000000000)⟩
def e156 : ℝ := (5969/25000000000000)
theorem h156 : Model (fun x => f156 ((83/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (183/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(112090108401083/100000000000000),(8213392601/2500000000000),(716511879/100000000000000),(-5825301/100000000000000)⟩
def e157 : ℝ := (235857/25000000000000)
theorem h157 : Model (fun x => f157 ((83/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(212090108401083/100000000000000),(8213392601/2500000000000),(716511879/100000000000000),(-5825301/100000000000000)⟩
def e158 : ℝ := (235857/25000000000000)
theorem h158 : Model (fun x => f158 ((83/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(106045054200541/100000000000000),(8213392601/5000000000000),(358255939/100000000000000),(-2912651/100000000000000)⟩
def e159 : ℝ := (117929/25000000000000)
theorem h159 : Model (fun x => f159 ((83/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(6045054200541/100000000000000),(8213392601/5000000000000),(358255939/100000000000000),(-2912651/100000000000000)⟩
def e160 : ℝ := (117929/25000000000000)
theorem h160 : Model (fun x => f160 ((83/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((83/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((83/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(391356747644853/100000000000000),(30311329837/5000000000000),(330533753/25000000000000),(-1074907/10000000000000)⟩
def e163 : ℝ := (87043/5000000000000)
theorem h163 : Model (fun x => f163 ((83/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(1373535516679569/50000000000000),(30311329837/5000000000000),(330533753/25000000000000),(-1074907/10000000000000)⟩
def e164 : ℝ := (1740861/100000000000000)
theorem h164 : Model (fun x => f164 ((83/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((83/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2913132966253059/100000000000000),(5155427903053/100000000000000),(3059859831/25000000000000),(-21766941/25000000000000)⟩
def e166 : ℝ := (14840861/100000000000000)
theorem h166 : Model (fun x => f166 ((83/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8195513918634011/100000000000000),(5155427903053/100000000000000),(3059859831/25000000000000),(-21766941/25000000000000)⟩
def e167 : ℝ := (7420431/50000000000000)
theorem h167 : Model (fun x => f167 ((83/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((83/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4345468588514159/50000000000000),(9464835495101/50000000000000),(6351118261/12500000000000),(-58492537/20000000000000)⟩
def e169 : ℝ := (54696369/100000000000000)
theorem h169 : Model (fun x => f169 ((83/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13959984796075937/100000000000000),(9464835495101/50000000000000),(6351118261/12500000000000),(-58492537/20000000000000)⟩
def e170 : ℝ := (5469637/10000000000000)
theorem h170 : Model (fun x => f170 ((83/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((83/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(1480387344338601/10000000000000),(5375718378547/12500000000000),(134988212963/100000000000000),(-113093683/20000000000000)⟩
def e172 : ℝ := (31221537/25000000000000)
theorem h172 : Model (fun x => f172 ((83/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(3427917545820059/20000000000000),(5375718378547/12500000000000),(134988212963/100000000000000),(-113093683/20000000000000)⟩
def e173 : ℝ := (124886149/100000000000000)
theorem h173 : Model (fun x => f173 ((83/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((83/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(9087842548536841/50000000000000),(14752060070653/20000000000000),(275196531449/100000000000000),(-36152739/5000000000000)⟩
def e175 : ℝ := (26924841/12500000000000)
theorem h175 : Model (fun x => f175 ((83/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(9289033024727317/50000000000000),(14752060070653/20000000000000),(275196531449/100000000000000),(-36152739/5000000000000)⟩
def e176 : ℝ := (215398729/100000000000000)
theorem h176 : Model (fun x => f176 ((83/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((83/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(2462640026444559/12500000000000),(108736940534397/100000000000000),(23977689847/5000000000000),(-591567973/100000000000000)⟩
def e178 : ℝ := (79780027/25000000000000)
theorem h178 : Model (fun x => f178 ((83/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(1230218822746089/6250000000000),(108736940534397/100000000000000),(23977689847/5000000000000),(-591567973/100000000000000)⟩
def e179 : ℝ := (319120109/100000000000000)
theorem h179 : Model (fun x => f179 ((83/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((83/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(20873379477861559/100000000000000),(147643812090043/100000000000000),(94710029047/12500000000000),(-23331003/100000000000000)⟩
def e181 : ℝ := (217369419/50000000000000)
theorem h181 : Model (fun x => f181 ((83/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(5219178202798723/25000000000000),(147643812090043/100000000000000),(94710029047/12500000000000),(-23331003/100000000000000)⟩
def e182 : ℝ := (434738839/100000000000000)
theorem h182 : Model (fun x => f182 ((83/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(1262008604728017/100000000000000),(21609438085961/50000000000000),(90781390747/25000000000000),(291022903/25000000000000)⟩
def e183 : ℝ := (12782113/10000000000000)
theorem h183 : Model (fun x => f183 ((83/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(28113883800989/25000000000000),(348395865417/100000000000000),(1029664681/100000000000000),(-2500223/50000000000000)⟩
def e184 : ℝ := (40413/4000000000000)
theorem h184 : Model (fun x => f184 ((83/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(206045054200541/100000000000000),(8213392601/5000000000000),(358255939/100000000000000),(-2912651/100000000000000)⟩
def e185 : ℝ := (117929/25000000000000)
theorem h185 : Model (fun x => f185 ((83/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(212272821802519/50000000000000),(676931569457/100000000000000),(1746176559/100000000000000),(-2706437/25000000000000)⟩
def e186 : ℝ := (1953757/100000000000000)
theorem h186 : Model (fun x => f186 ((83/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(218688825368009/25000000000000),(1046088014391/50000000000000),(778856421/12500000000000),(-29377897/100000000000000)⟩
def e187 : ℝ := (6066023/100000000000000)
theorem h187 : Model (fun x => f187 ((83/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(901195017520081/50000000000000),(5747766976633/100000000000000),(485224913/2500000000000),(-68279643/100000000000000)⟩
def e188 : ℝ := (16732151/100000000000000)
theorem h188 : Model (fun x => f188 ((83/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(126680460022949/6250000000000),(1592891809577/12500000000000),(60410047019/100000000000000),(-40108911/100000000000000)⟩
def e189 : ℝ := (9367523/25000000000000)
theorem h189 : Model (fun x => f189 ((83/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((83/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(106045054200541/12500000000000),(8213392601/625000000000),(358255939/12500000000000),(-2912651/12500000000000)⟩
def e191 : ℝ := (117929/3125000000000)
theorem h191 : Model (fun x => f191 ((83/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(240203992202071/25000000000000),(1662538681577/100000000000000),(3895712193/100000000000000),(-14150827/50000000000000)⟩
def e192 : ℝ := (4784053/100000000000000)
theorem h192 : Model (fun x => f192 ((83/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(265203992202071/25000000000000),(1662538681577/100000000000000),(3895712193/100000000000000),(-14150827/50000000000000)⟩
def e193 : ℝ := (4784053/100000000000000)
theorem h193 : Model (fun x => f193 ((83/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(21501544788531797/100000000000000),(33775798370551/20000000000000),(931660663497/100000000000000),(250825931/50000000000000)⟩
def e194 : ℝ := (248815829/50000000000000)
theorem h194 : Model (fun x => f194 ((83/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(465082862573/100000000000000),(-228305471/6250000000000),(8538761/100000000000000),(40181/50000000000000)⟩
def e195 : ℝ := (1483/12500000000000)
theorem h195 : Model (fun x => f195 ((83/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (853269325469281/4000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(2934692872393/50000000000000),(77451915723/50000000000000),(5446443/2500000000000),(-1573023/50000000000000)⟩
def e196 : ℝ := (38883/5000000000000)
theorem h196 : Model (fun x => f196 ((83/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(112090108401083/50000000000000),(8213392601/1250000000000),(716511879/50000000000000),(-5825301/50000000000000)⟩
def e197 : ℝ := (235857/12500000000000)
theorem h197 : Model (fun x => f197 ((83/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(1885990831989/4000000000000),(-73036801489/100000000000000),(-5768877/12500000000000),(322651/20000000000000)⟩
def e198 : ℝ := (214751/100000000000000)
theorem h198 : Model (fun x => f198 ((83/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (42352169883287/20000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(105700458400547/100000000000000),(4564800093/3125000000000),(92302029/100000000000000),(-1613257/50000000000000)⟩
def e199 : ℝ := (1392351/100000000000000)
theorem h199 : Model (fun x => f199 ((83/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(5700458400547/100000000000000),(4564800093/3125000000000),(92302029/100000000000000),(-1613257/50000000000000)⟩
def e200 : ℝ := (1392351/100000000000000)
theorem h200 : Model (fun x => f200 ((83/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(390085025049637/100000000000000),(6738514423/1250000000000),(8515961/2500000000000),(-5953687/50000000000000)⟩
def e201 : ℝ := (5138441/100000000000000)
theorem h201 : Model (fun x => f201 ((83/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(1372899655381961/50000000000000),(6738514423/1250000000000),(8515961/2500000000000),(-5953687/50000000000000)⟩
def e202 : ℝ := (2569221/50000000000000)
theorem h202 : Model (fun x => f202 ((83/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(116092898329461/4000000000000),(2290349617241/50000000000000),(3681940133/100000000000000),(-100184583/100000000000000)⟩
def e203 : ℝ := (1092801/2500000000000)
theorem h203 : Model (fun x => f203 ((83/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8184703410617477/100000000000000),(2290349617241/50000000000000),(3681940133/100000000000000),(-100184583/100000000000000)⟩
def e204 : ℝ := (43712041/100000000000000)
theorem h204 : Model (fun x => f204 ((83/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8651269023747877/100000000000000),(8398755626793/50000000000000),(18137667327/100000000000000),(-22523109/6250000000000)⟩
def e205 : ℝ := (20072789/12500000000000)
theorem h205 : Model (fun x => f205 ((83/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(1740039580349437/12500000000000),(8398755626793/50000000000000),(18137667327/100000000000000),(-22523109/6250000000000)⟩
def e206 : ℝ := (160582313/100000000000000)
theorem h206 : Model (fun x => f206 ((83/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(14713838502242473/100000000000000),(38088954460723/100000000000000),(5655706211/10000000000000),(-788054649/100000000000000)⟩
def e207 : ℝ := (18253867/5000000000000)
theorem h207 : Model (fun x => f207 ((83/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8524776393978379/50000000000000),(38088954460723/100000000000000),(5655706211/10000000000000),(-788054649/100000000000000)⟩
def e208 : ℝ := (365077341/100000000000000)
theorem h208 : Model (fun x => f208 ((83/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(9010727726056767/50000000000000),(65165095513623/100000000000000),(131156065183/100000000000000),(-158163971/12500000000000)⟩
def e209 : ℝ := (626673269/100000000000000)
theorem h209 : Model (fun x => f209 ((83/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(9211918202247243/50000000000000),(65165095513623/100000000000000),(131156065183/100000000000000),(-158163971/12500000000000)⟩
def e210 : ℝ := (62667327/10000000000000)
theorem h210 : Model (fun x => f210 ((83/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2434259941814691/12500000000000),(47896083158751/50000000000000),(250827139839/100000000000000),(-336030981/20000000000000)⟩
def e211 : ℝ := (462290701/50000000000000)
theorem h211 : Model (fun x => f211 ((83/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(243205756086231/1250000000000),(47896083158751/50000000000000),(250827139839/100000000000000),(-336030981/20000000000000)⟩
def e212 : ℝ := (924581403/100000000000000)
theorem h212 : Model (fun x => f212 ((83/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(160668499399789/781250000000),(32418377938557/25000000000000),(52876401639/12500000000000),(-389777301/20000000000000)⟩
def e213 : ℝ := (62810047/5000000000000)
theorem h213 : Model (fun x => f213 ((83/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(822756050260253/4000000000000),(32418377938557/25000000000000),(52876401639/12500000000000),(-389777301/20000000000000)⟩
def e214 : ℝ := (1256200941/100000000000000)
theorem h214 : Model (fun x => f214 ((83/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(293130414894183/25000000000000),(1169928742251/3125000000000),(2906473277/1250000000000),(-37154941/100000000000000)⟩
def e215 : ℝ := (73660789/20000000000000)
theorem h215 : Model (fun x => f215 ((83/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(111725869060857/100000000000000),(61760187179/20000000000000),(40850231/10000000000000),(-6551223/100000000000000)⟩
def e216 : ℝ := (2956863/100000000000000)
theorem h216 : Model (fun x => f216 ((83/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(205700458400547/100000000000000),(4564800093/3125000000000),(92302029/100000000000000),(-1613257/50000000000000)⟩
def e217 : ℝ := (1392351/100000000000000)
theorem h217 : Model (fun x => f217 ((83/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(423126785861951/100000000000000),(600948141847/100000000000000),(9267287/1562500000000),(-13004251/100000000000000)⟩
def e218 : ℝ := (1148313/20000000000000)
theorem h218 : Model (fun x => f218 ((83/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(435186869066767/50000000000000),(1854229623793/100000000000000),(2488403729/100000000000000),(-3898099/10000000000000)⟩
def e219 : ℝ := (710259/4000000000000)
theorem h219 : Model (fun x => f219 ((83/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(358072553827731/20000000000000),(5085545114589/100000000000000),(2157642629/25000000000000),(-51460207/50000000000000)⟩
def e220 : ℝ := (48810207/100000000000000)
theorem h220 : Model (fun x => f220 ((83/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2000298363162187/100000000000000),(2802631615693/25000000000000),(8165116023/25000000000000),(-184853533/100000000000000)⟩
def e221 : ℝ := (54195243/50000000000000)
theorem h221 : Model (fun x => f221 ((83/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(105700458400547/12500000000000),(4564800093/390625000000),(92302029/12500000000000),(-1613257/6250000000000)⟩
def e222 : ℝ := (1392351/12500000000000)
theorem h222 : Model (fun x => f222 ((83/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(957329536265233/100000000000000),(1477389759703/100000000000000),(573459271/50000000000000),(-6472667/20000000000000)⟩
def e223 : ℝ := (14095671/100000000000000)
theorem h223 : Model (fun x => f223 ((83/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1057329536265233/100000000000000),(1477389759703/100000000000000),(573459271/50000000000000),(-6472667/20000000000000)⟩
def e224 : ℝ := (14095671/100000000000000)
theorem h224 : Model (fun x => f224 ((83/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(10574872703571899/50000000000000),(148084410642583/100000000000000),(266946848159/50000000000000),(-398155261/20000000000000)⟩
def e225 : ℝ := (1437184841/100000000000000)
theorem h225 : Model (fun x => f225 ((83/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(236409465161/50000000000000),(-3310541631/100000000000000),(11243849/100000000000000),(12337/25000000000000)⟩
def e226 : ℝ := (6707/20000000000000)
theorem h226 : Model (fun x => f226 ((83/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (21001123674843751/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1385976092151/25000000000000),(27639161679/20000000000000),(-1633253/20000000000000),(-154261/5000000000000)⟩
def e227 : ℝ := (441089/20000000000000)
theorem h227 : Model (fun x => f227 ((83/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(1141329011339/10000000000000),(293099639841/100000000000000),(41938291/20000000000000),(-3115633/50000000000000)⟩
def e228 : ℝ := (596621/20000000000000)
theorem h228 : Model (fun x => f228 ((83/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(13861317450657/100000000000000),(29224100223/10000000000000),(-75723429/10000000000000),(1531983/100000000000000)⟩
def e229 : ℝ := (27286757/100000000000000)
theorem h229 : Model (fun x => f229 ((83/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(1670038247067/25000000000000),(15088816569/25000000000000),(-1092104071/100000000000000),(2779237/20000000000000)⟩
def e230 : ℝ := (13765031/100000000000000)
theorem h230 : Model (fun x => f230 ((83/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-147054657298281/100000000000000),(-571201180679/50000000000000),(23135354469/100000000000000),(-320537677/100000000000000)⟩
def e231 : ℝ := (35488907/100000000000000)
theorem h231 : Model (fun x => f231 ((83/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((83/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-6889/320),(-83/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((83/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1743/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((83/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1411/64),(1/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((83/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((83/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3075/64),(1/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((83/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((83/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(384375/32),(25/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((83/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(13031/1600),(37/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((83/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(22631/1600),(37/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((83/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((83/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4277259/1600),(6993/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((83/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(37407133867/100000000000000),(-61157879/50000000000000),(2052869/100000000000000),(-6059/50000000000000)⟩
def e244 : ℝ := (27/20000000000000)
theorem h244 : Model (fun x => f244 ((83/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1065771/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(449323971254003/100000000000000),(-705386918561/50000000000000),(-4756956647/100000000000000),(-9358243/20000000000000)⟩
def e245 : ℝ := (1627053/50000000000000)
theorem h245 : Model (fun x => f245 ((83/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(747/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((83/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(66649/1600),(443/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((83/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(100249/1600),(443/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((83/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(26569/1600),(163/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((83/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2663515681/2560000),(14055327/640000),(207827/1280000),(303/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((83/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((83/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(136161/160),(1107/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((83/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(117507950147/100000000000000),(-1910698377/100000000000000),(23301199/100000000000000),(-63147/25000000000000)⟩
def e253 : ℝ := (2629/100000000000000)
theorem h253 : Model (fun x => f253 ((83/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (66969/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(7641217477019/6250000000000),(296342884543/50000000000000),(1360858001/100000000000000),(-1134219/20000000000000)⟩
def e254 : ℝ := (553873/10000000000000)
theorem h254 : Model (fun x => f254 ((83/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(13891217477019/6250000000000),(296342884543/50000000000000),(1360858001/100000000000000),(-1134219/20000000000000)⟩
def e255 : ℝ := (553873/10000000000000)
theorem h255 : Model (fun x => f255 ((83/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(13891217477019/12500000000000),(296342884543/100000000000000),(680429/100000000000),(-708887/25000000000000)⟩
def e256 : ℝ := (1384683/50000000000000)
theorem h256 : Model (fun x => f256 ((83/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(1391217477019/12500000000000),(296342884543/100000000000000),(680429/100000000000),(-708887/25000000000000)⟩
def e257 : ℝ := (1384683/50000000000000)
theorem h257 : Model (fun x => f257 ((83/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(205060829422661/50000000000000),(546823179811/50000000000000),(2511107023/100000000000000),(-10464523/100000000000000)⟩
def e258 : ℝ := (10220283/100000000000000)
theorem h258 : Model (fun x => f258 ((83/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2765835944559607/100000000000000),(546823179811/50000000000000),(2511107023/100000000000000),(-10464523/100000000000000)⟩
def e259 : ℝ := (2555071/25000000000000)
theorem h259 : Model (fun x => f259 ((83/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3073666288930701/100000000000000),(9411724373791/100000000000000),(24851079729/100000000000000),(-7517283/10000000000000)⟩
def e260 : ℝ := (8805969/10000000000000)
theorem h260 : Model (fun x => f260 ((83/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8356047241311653/100000000000000),(9411724373791/100000000000000),(24851079729/100000000000000),(-7517283/10000000000000)⟩
def e261 : ℝ := (88059691/100000000000000)
theorem h261 : Model (fun x => f261 ((83/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4643026779092193/50000000000000),(17610888118743/50000000000000),(56182442211/50000000000000),(-182794593/100000000000000)⟩
def e262 : ℝ := (66022941/20000000000000)
theorem h262 : Model (fun x => f262 ((83/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(2911020235446401/20000000000000),(17610888118743/50000000000000),(56182442211/50000000000000),(-182794593/100000000000000)⟩
def e263 : ℝ := (165057353/50000000000000)
theorem h263 : Model (fun x => f263 ((83/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(16175046068235603/100000000000000),(41137437484053/50000000000000),(328285160781/100000000000000),(-43211517/100000000000000)⟩
def e264 : ℝ := (154535803/20000000000000)
theorem h264 : Model (fun x => f264 ((83/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(289230630530467/1562500000000),(41137437484053/50000000000000),(328285160781/100000000000000),(-43211517/100000000000000)⟩
def e265 : ℝ := (96584877/12500000000000)
theorem h265 : Model (fun x => f265 ((83/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(20570959819335927/100000000000000),(146287175669857/100000000000000),(367295382167/50000000000000),(479884741/50000000000000)⟩
def e266 : ℝ := (688063203/50000000000000)
theorem h266 : Model (fun x => f266 ((83/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(20973340771716879/100000000000000),(146287175669857/100000000000000),(367295382167/50000000000000),(479884741/50000000000000)⟩
def e267 : ℝ := (1376126407/100000000000000)
theorem h267 : Model (fun x => f267 ((83/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(23307619030363893/100000000000000),(28090195091781/12500000000000),(1392569134093/100000000000000),(364416801/10000000000000)⟩
def e268 : ℝ := (1060991109/50000000000000)
theorem h268 : Model (fun x => f268 ((83/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(4657999996548969/20000000000000),(28090195091781/12500000000000),(1392569134093/100000000000000),(364416801/10000000000000)⟩
def e269 : ℝ := (2121982219/100000000000000)
theorem h269 : Model (fun x => f269 ((83/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(25882116384006191/100000000000000),(9960960734803/3125000000000),(237197672473/10000000000000),(2261301377/25000000000000)⟩
def e270 : ℝ := (121184839/4000000000000)
theorem h270 : Model (fun x => f270 ((83/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(6471362429334881/25000000000000),(9960960734803/3125000000000),(237197672473/10000000000000),(2261301377/25000000000000)⟩
def e271 : ℝ := (189351311/6250000000000)
theorem h271 : Model (fun x => f271 ((83/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1440491601890371/50000000000000),(3505806774513/3125000000000),(27694441849/2000000000000),(947077023/10000000000000)⟩
def e272 : ℝ := (55292801/5000000000000)
theorem h272 : Model (fun x => f272 ((83/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(15437273839507/12500000000000),(82331269139/12500000000000),(1195254503/50000000000000),(-2269469/100000000000000)⟩
def e273 : ℝ := (772981/12500000000000)
theorem h273 : Model (fun x => f273 ((83/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(26391217477019/12500000000000),(296342884543/100000000000000),(680429/100000000000),(-708887/25000000000000)⟩
def e274 : ℝ := (1384683/50000000000000)
theorem h274 : Model (fun x => f274 ((83/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(11143941758709/2500000000000),(625667961099/50000000000000),(1875683503/50000000000000),(-1588113/20000000000000)⟩
def e275 : ℝ := (586129/5000000000000)
theorem h275 : Model (fun x => f275 ((83/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(941127009617033/100000000000000),(495364176893/12500000000000),(586462433/4000000000000),(-4886603/50000000000000)⟩
def e276 : ℝ := (37197743/100000000000000)
theorem h276 : Model (fun x => f276 ((83/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1986999006743973/100000000000000),(2231170342009/20000000000000),(49102428249/100000000000000),(23093051/100000000000000)⟩
def e277 : ℝ := (13107681/12500000000000)
theorem h277 : Model (fun x => f277 ((83/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(245390782287481/10000000000000),(6716161755281/25000000000000),(181618035059/100000000000000),(17922501/3125000000000)⟩
def e278 : ℝ := (254834361/100000000000000)
theorem h278 : Model (fun x => f278 ((83/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(13891217477019/1562500000000),(296342884543/12500000000000),(680429/12500000000),(-708887/3125000000000)⟩
def e279 : ℝ := (1384683/6250000000000)
theorem h279 : Model (fun x => f279 ((83/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(126567013655659/12500000000000),(189337076841/6250000000000),(3916970503/50000000000000),(-24953853/100000000000000)⟩
def e280 : ℝ := (3542347/12500000000000)
theorem h280 : Model (fun x => f280 ((83/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(139067013655659/12500000000000),(189337076841/6250000000000),(3916970503/50000000000000),(-24953853/100000000000000)⟩
def e281 : ℝ := (3542347/12500000000000)
theorem h281 : Model (fun x => f281 ((83/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(27300610617076771/100000000000000),(373217416174549/100000000000000),(3026639710093/100000000000000),(2674951591/20000000000000)⟩
def e282 : ℝ := (3570835303/100000000000000)
theorem h282 : Model (fun x => f282 ((83/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(36629217347/10000000000000),(-1251864111/25000000000000),(1740427/6250000000000),(-499/10000000000000)⟩
def e283 : ℝ := (12459/25000000000000)
theorem h283 : Model (fun x => f283 ((83/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (26924349615598871/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(5276407997217/50000000000000),(16666492971/6250000000000),(256735289/100000000000000),(-3552231/100000000000000)⟩
def e284 : ℝ := (5695531/100000000000000)
theorem h284 : Model (fun x => f284 ((83/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(7641217477019/3125000000000),(296342884543/25000000000000),(1360858001/50000000000000),(-1134219/10000000000000)⟩
def e285 : ℝ := (553873/5000000000000)
theorem h285 : Model (fun x => f285 ((83/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(8998491327833/20000000000000),(-119978634029/100000000000000),(1778333/4000000000000),(882033/50000000000000)⟩
def e286 : ℝ := (1135293/100000000000000)
theorem h286 : Model (fun x => f286 ((83/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (3463522215553/1562500000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(55007543360833/50000000000000),(239957268057/100000000000000),(-17783331/20000000000000),(-441017/12500000000000)⟩
def e287 : ℝ := (7822587/100000000000000)
theorem h287 : Model (fun x => f287 ((83/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(5007543360833/50000000000000),(239957268057/100000000000000),(-17783331/20000000000000),(-441017/12500000000000)⟩
def e288 : ℝ := (7822587/100000000000000)
theorem h288 : Model (fun x => f288 ((83/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(406008058139481/100000000000000),(55347286531/6250000000000),(-328144799/100000000000000),(-6510251/50000000000000)⟩
def e289 : ℝ := (28869073/100000000000000)
theorem h289 : Model (fun x => f289 ((83/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(1380861171926883/50000000000000),(55347286531/6250000000000),(-328144799/100000000000000),(-6510251/50000000000000)⟩
def e290 : ℝ := (14434537/50000000000000)
theorem h290 : Model (fun x => f290 ((83/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(3038311231602347/100000000000000),(7601199332033/100000000000000),(-691682527/100000000000000),(-28334163/25000000000000)⟩
def e291 : ℝ := (49599859/20000000000000)
theorem h291 : Model (fun x => f291 ((83/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8320692183983299/100000000000000),(7601199332033/100000000000000),(-691682527/100000000000000),(-28334163/25000000000000)⟩
def e292 : ℝ := (3874989/1562500000000)
theorem h292 : Model (fun x => f292 ((83/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(9154016722052111/100000000000000),(28328571685141/100000000000000),(10080193961/100000000000000),(-106667807/25000000000000)⟩
def e293 : ℝ := (925459697/100000000000000)
theorem h293 : Model (fun x => f293 ((83/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(1442306434109973/10000000000000),(28328571685141/100000000000000),(10080193961/100000000000000),(-106667807/25000000000000)⟩
def e294 : ℝ := (462729849/50000000000000)
theorem h294 : Model (fun x => f294 ((83/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(1983443342847819/12500000000000),(65774893869423/100000000000000),(33120847231/50000000000000),(-244817177/25000000000000)⟩
def e295 : ℝ := (1076436417/50000000000000)
theorem h295 : Model (fun x => f295 ((83/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(18203261028496837/100000000000000),(65774893869423/100000000000000),(33120847231/50000000000000),(-244817177/25000000000000)⟩
def e296 : ℝ := (430574567/20000000000000)
theorem h296 : Model (fun x => f296 ((83/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(801053336266881/4000000000000),(23208470878559/20000000000000),(214521765197/100000000000000),(-1619112199/100000000000000)⟩
def e297 : ℝ := (1903750197/50000000000000)
theorem h297 : Model (fun x => f297 ((83/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(20428714359052977/100000000000000),(23208470878559/20000000000000),(214521765197/100000000000000),(-1619112199/100000000000000)⟩
def e298 : ℝ := (761500079/20000000000000)
theorem h298 : Model (fun x => f298 ((83/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(22474667818233567/100000000000000),(22085535211781/12500000000000),(24814691997/5000000000000),(-2090440929/100000000000000)⟩
def e299 : ℝ := (726661209/12500000000000)
theorem h299 : Model (fun x => f299 ((83/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(22457048770614519/100000000000000),(22085535211781/12500000000000),(24814691997/5000000000000),(-2090440929/100000000000000)⟩
def e300 : ℝ := (5813289673/100000000000000)
theorem h300 : Model (fun x => f300 ((83/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(24706141680118391/100000000000000),(124133343222837/50000000000000),(189999363453/20000000000000),(-2058324237/100000000000000)⟩
def e301 : ℝ := (8191740203/100000000000000)
theorem h301 : Model (fun x => f301 ((83/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(6177368753362931/25000000000000),(124133343222837/50000000000000),(189999363453/20000000000000),(-2058324237/100000000000000)⟩
def e302 : ℝ := (2047935051/25000000000000)
theorem h302 : Model (fun x => f302 ((83/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(2474675351065581/100000000000000),(42078152571023/50000000000000),(334453062371/50000000000000),(196181827/20000000000000)⟩
def e303 : ℝ := (2807065061/100000000000000)
theorem h303 : Model (fun x => f303 ((83/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(30258298265939/25000000000000),(105595678619/20000000000000),(190075717/50000000000000),(-1023711/12500000000000)⟩
def e304 : ℝ := (17266471/100000000000000)
theorem h304 : Model (fun x => f304 ((83/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(105007543360833/50000000000000),(239957268057/100000000000000),(-17783331/20000000000000),(-441017/12500000000000)⟩
def e305 : ℝ := (7822587/100000000000000)
theorem h305 : Model (fun x => f305 ((83/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(27566460406693/6250000000000),(1007892929209/100000000000000),(50579531/25000000000000),(-381149/2500000000000)⟩
def e306 : ℝ := (6582329/20000000000000)
theorem h306 : Model (fun x => f306 ((83/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(5789372572921/625000000000),(317509081401/10000000000000),(2451232129/100000000000000),(-1199771/2500000000000)⟩
def e307 : ℝ := (51926093/50000000000000)
theorem h307 : Model (fun x => f307 ((83/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1945368932745661/100000000000000),(4445446484357/50000000000000),(11943183827/100000000000000),(-13041039/10000000000000)⟩
def e308 : ℝ := (291293133/100000000000000)
theorem h308 : Model (fun x => f308 ((83/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(470908427234477/20000000000000),(4206411856559/20000000000000),(68792558461/100000000000000),(-110151609/50000000000000)⟩
def e309 : ℝ := (692907077/100000000000000)
theorem h309 : Model (fun x => f309 ((83/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(55007543360833/6250000000000),(239957268057/12500000000000),(-17783331/2500000000000),(-441017/1562500000000)⟩
def e310 : ℝ := (7822587/12500000000000)
theorem h310 : Model (fun x => f310 ((83/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(250288471709271/25000000000000),(2447636537551/100000000000000),(-165590903/50000000000000),(-4551847/12500000000000)⟩
def e311 : ℝ := (79847167/100000000000000)
theorem h311 : Model (fun x => f311 ((83/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(275288471709271/25000000000000),(2447636537551/100000000000000),(-165590903/50000000000000),(-4551847/12500000000000)⟩
def e312 : ℝ := (79847167/100000000000000)
theorem h312 : Model (fun x => f312 ((83/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(6481783062419781/25000000000000),(57845194378273/20000000000000),(1264502483783/100000000000000),(-1669141251/100000000000000)⟩
def e313 : ℝ := (955712319/10000000000000)
theorem h313 : Model (fun x => f313 ((83/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(192848169703/50000000000000),(-3442059/80000000000),(14592861/50000000000000),(-11363/12500000000000)⟩
def e314 : ℝ := (73051/50000000000000)
theorem h314 : Model (fun x => f314 ((83/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (5127326109807907/20000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(4772366120621/50000000000000),(218113056259/100000000000000),(-318688789/100000000000000),(-2684803/100000000000000)⟩
def e315 : ℝ := (14764677/100000000000000)
theorem h315 : Model (fun x => f315 ((83/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(5024387058919/25000000000000),(96955388759/20000000000000),(-123907/200000000000),(-3118517/50000000000000)⟩
def e316 : ℝ := (1278763/6250000000000)
theorem h316 : Model (fun x => f316 ((83/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(22575775464307/25000000000000),(1894688063171/100000000000000),(-64588079/800000000000),(-29807491/50000000000000)⟩
def e317 : ℝ := (93028249/100000000000000)
theorem h317 : Model (fun x => f317 ((83/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(43519567160109/100000000000000),(194385273293/50000000000000),(-4287415311/50000000000000),(745811/1000000000000)⟩
def e318 : ℝ := (48145643/100000000000000)
theorem h318 : Model (fun x => f318 ((83/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-25883772534543/25000000000000),(-188407953693/25000000000000),(14560523847/100000000000000),(-245956577/100000000000000)⟩
def e319 : ℝ := (1672691/2000000000000)
theorem h319 : Model (fun x => f319 ((83/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((83/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-75779/1600),(-913/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((83/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((83/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(8051/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((83/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(246261/1600),(1027/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((83/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((83/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(419061/1600),(1027/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((83/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2095305/32),(5135/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((83/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((83/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1035359554651009077/100000000000000),(338547156750363/10000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (13411/10000000000000)
theorem h329 : Model (fun x => f329 ((83/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9658480433/100000000000000),(-31581793/100000000000000),(4141/781250000000),(-3129/100000000000000)⟩
def e330 : ℝ := (9/25000000000000)
theorem h330 : Model (fun x => f330 ((83/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (51596416673379713/5000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(126484139647919/20000000000000),(257961759883/25000000000000),(1992584271/25000000000000),(2438993/12500000000000)⟩
def e331 : ℝ := (4289449/100000000000000)
theorem h331 : Model (fun x => f331 ((83/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((83/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(443/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((83/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((83/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((83/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(665806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((83/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((83/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((83/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2953845709717177/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1057/100000000000000)
theorem h339 : Model (fun x => f339 ((83/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3764193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((83/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((83/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((83/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(530288572570641/25000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1057/100000000000000)
theorem h343 : Model (fun x => f343 ((83/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(58930178051/1250000000000),(-313109199/5000000000000),(1663619/20000000000000),(-11049/100000000000000)⟩
def e344 : ℝ := (19/100000000000000)
theorem h344 : Model (fun x => f344 ((83/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1059168374323513/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(34814130721763/25000000000000),(860797724043/100000000000000),(-571701331/50000000000000),(1518787/100000000000000)⟩
def e345 : ℝ := (767/25000000000000)
theorem h345 : Model (fun x => f345 ((83/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(59814130721763/25000000000000),(860797724043/100000000000000),(-571701331/50000000000000),(1518787/100000000000000)⟩
def e346 : ℝ := (767/25000000000000)
theorem h346 : Model (fun x => f346 ((83/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(59814130721763/50000000000000),(430398862021/100000000000000),(-571701331/100000000000000),(759393/100000000000000)⟩
def e347 : ℝ := (307/20000000000000)
theorem h347 : Model (fun x => f347 ((83/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(9814130721763/50000000000000),(430398862021/100000000000000),(-571701331/100000000000000),(759393/100000000000000)⟩
def e348 : ℝ := (307/20000000000000)
theorem h348 : Model (fun x => f348 ((83/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(441485250565393/100000000000000),(198547094087/12500000000000),(-2109850151/100000000000000),(2802521/100000000000000)⟩
def e349 : ℝ := (1417/25000000000000)
theorem h349 : Model (fun x => f349 ((83/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(1398599768139839/50000000000000),(198547094087/12500000000000),(-2109850151/100000000000000),(2802521/100000000000000)⟩
def e350 : ℝ := (5669/100000000000000)
theorem h350 : Model (fun x => f350 ((83/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(13384964697431/400000000000),(13939262467027/100000000000000),(-11679248567/100000000000000),(3216401/50000000000000)⟩
def e351 : ℝ := (85989/100000000000000)
theorem h351 : Model (fun x => f351 ((83/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(4314311063369351/50000000000000),(13939262467027/100000000000000),(-11679248567/100000000000000),(3216401/50000000000000)⟩
def e352 : ℝ := (8599/10000000000000)
theorem h352 : Model (fun x => f352 ((83/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(10322270636748907/100000000000000),(53812788788929/100000000000000),(-826800631/25000000000000),(-56737701/100000000000000)⟩
def e353 : ℝ := (218171/50000000000000)
theorem h353 : Model (fun x => f353 ((83/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(7795659127898263/50000000000000),(53812788788929/100000000000000),(-826800631/25000000000000),(-56737701/100000000000000)⟩
def e354 : ℝ := (436343/100000000000000)
theorem h354 : Model (fun x => f354 ((83/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(3730324593107293/20000000000000),(131480160009493/100000000000000),(69258753849/50000000000000),(-135678769/50000000000000)⟩
def e355 : ℝ := (189537/20000000000000)
theorem h355 : Model (fun x => f355 ((83/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(83949349005003/400000000000),(131480160009493/100000000000000),(69258753849/50000000000000),(-135678769/50000000000000)⟩
def e356 : ℝ := (473843/50000000000000)
theorem h356 : Model (fun x => f356 ((83/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(2510678667696077/10000000000000),(49523338052083/20000000000000),(611610312311/100000000000000),(-320739983/100000000000000)⟩
def e357 : ℝ := (1212971/50000000000000)
theorem h357 : Model (fun x => f357 ((83/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(12754583814670861/50000000000000),(49523338052083/20000000000000),(611610312311/100000000000000),(-320739983/100000000000000)⟩
def e358 : ℝ := (2425943/100000000000000)
theorem h358 : Model (fun x => f358 ((83/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(15258086871848109/50000000000000),(406010708790251/100000000000000),(1651561949617/100000000000000),(513377539/50000000000000)⟩
def e359 : ℝ := (6311089/100000000000000)
theorem h359 : Model (fun x => f359 ((83/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(3049855469607717/10000000000000),(406010708790251/100000000000000),(1651561949617/100000000000000),(513377539/50000000000000)⟩
def e360 : ℝ := (631109/10000000000000)
theorem h360 : Model (fun x => f360 ((83/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(36484890748319973/100000000000000),(308484492272541/50000000000000),(3548839674173/100000000000000),(6247028349/100000000000000)⟩
def e361 : ℝ := (9997781/100000000000000)
theorem h361 : Model (fun x => f361 ((83/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(18244112040826653/50000000000000),(308484492272541/50000000000000),(3548839674173/100000000000000),(6247028349/100000000000000)⟩
def e362 : ℝ := (4998891/50000000000000)
theorem h362 : Model (fun x => f362 ((83/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(1790501004711631/25000000000000),(69536296632771/25000000000000),(3143399355229/100000000000000),(1656277219/12500000000000)⟩
def e363 : ℝ := (13867507/100000000000000)
theorem h363 : Model (fun x => f363 ((83/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(71554604680003/50000000000000),(128719668977/12500000000000),(242299539/50000000000000),(-620859/20000000000000)⟩
def e364 : ℝ := (6751/50000000000000)
theorem h364 : Model (fun x => f364 ((83/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(109814130721763/50000000000000),(430398862021/100000000000000),(-571701331/100000000000000),(759393/100000000000000)⟩
def e365 : ℝ := (307/20000000000000)
theorem h365 : Model (fun x => f365 ((83/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(241182866123529/50000000000000),(945277537929/50000000000000),(-5146903/781250000000),(-1585509/100000000000000)⟩
def e366 : ℝ := (4143/25000000000000)
theorem h366 : Model (fun x => f366 ((83/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1059411471533547/100000000000000),(6228289867109/100000000000000),(1966158681/50000000000000),(-6731493/50000000000000)⟩
def e367 : ℝ := (55207/100000000000000)
theorem h367 : Model (fun x => f367 ((83/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(581691749115601/25000000000000),(3647755934079/20000000000000),(7346574871/25000000000000),(-40205993/100000000000000)⟩
def e368 : ℝ := (171083/100000000000000)
theorem h368 : Model (fun x => f368 ((83/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(665963570457381/20000000000000),(10012285517783/20000000000000),(241145166801/100000000000000),(261224347/100000000000000)⟩
def e369 : ℝ := (1402139/100000000000000)
theorem h369 : Model (fun x => f369 ((83/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(59814130721763/6250000000000),(430398862021/12500000000000),(-571701331/12500000000000),(759393/12500000000000)⟩
def e370 : ℝ := (307/2500000000000)
theorem h370 : Model (fun x => f370 ((83/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(550067650454107/50000000000000),(279559265499/6250000000000),(-408901157/10000000000000),(2970849/100000000000000)⟩
def e371 : ℝ := (12891/50000000000000)
theorem h371 : Model (fun x => f371 ((83/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(600067650454107/50000000000000),(279559265499/6250000000000),(-408901157/10000000000000),(2970849/100000000000000)⟩
def e372 : ℝ := (12891/50000000000000)
theorem h372 : Model (fun x => f372 ((83/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(9990579875309719/25000000000000),(374872946959049/50000000000000),(4997133384227/100000000000000),(1197325041/10000000000000)⟩
def e373 : ℝ := (10538277/50000000000000)
theorem h373 : Model (fun x => f373 ((83/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(250235725173/100000000000000),(-4694752703/100000000000000),(3549297/6250000000000),(-276673/50000000000000)⟩
def e374 : ℝ := (497/10000000000000)
theorem h374 : Model (fun x => f374 ((83/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (39207564479609587/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(448047317337/2500000000000),(179890123643/50000000000000),(-1125107791/100000000000000),(3906469/100000000000000)⟩
def e375 : ℝ := (79131/10000000000000)
theorem h375 : Model (fun x => f375 ((83/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(34814130721763/12500000000000),(860797724043/50000000000000),(-571701331/25000000000000),(1518787/50000000000000)⟩
def e376 : ℝ := (767/12500000000000)
theorem h376 : Model (fun x => f376 ((83/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(41796143650891/100000000000000),(-150374271491/100000000000000),(740759961/100000000000000),(-456133/12500000000000)⟩
def e377 : ℝ := (18251/100000000000000)
theorem h377 : Model (fun x => f377 ((83/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (59598645059623/25000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(14550964087277/12500000000000),(300748542979/100000000000000),(-1481519923/100000000000000),(3649063/50000000000000)⟩
def e378 : ℝ := (138157/100000000000000)
theorem h378 : Model (fun x => f378 ((83/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(2050964087277/12500000000000),(300748542979/100000000000000),(-1481519923/100000000000000),(3649063/50000000000000)⟩
def e379 : ℝ := (138157/100000000000000)
theorem h379 : Model (fun x => f379 ((83/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(429599892100559/100000000000000),(34684541787/3125000000000),(-2733757001/50000000000000),(673339/2500000000000)⟩
def e380 : ℝ := (509867/100000000000000)
theorem h380 : Model (fun x => f380 ((83/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(696328544453711/25000000000000),(34684541787/3125000000000),(-2733757001/50000000000000),(673339/2500000000000)⟩
def e381 : ℝ := (127467/25000000000000)
theorem h381 : Model (fun x => f381 ((83/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(162116026292669/5000000000000),(4721097277/48828125000),(-11072892081/25000000000000),(201741541/100000000000000)⟩
def e382 : ℝ := (187541/4000000000000)
theorem h382 : Model (fun x => f382 ((83/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2131175369558583/25000000000000),(4721097277/48828125000),(-11072892081/25000000000000),(201741541/100000000000000)⟩
def e383 : ℝ := (2344263/50000000000000)
theorem h383 : Model (fun x => f383 ((83/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(9923410005163593/100000000000000),(36893152822937/100000000000000),(-148775155533/100000000000000),(72566827/12500000000000)⟩
def e384 : ℝ := (19237671/100000000000000)
theorem h384 : Model (fun x => f384 ((83/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(3798114406052803/25000000000000),(36893152822937/100000000000000),(-148775155533/100000000000000),(72566827/12500000000000)⟩
def e385 : ℝ := (2404709/12500000000000)
theorem h385 : Model (fun x => f385 ((83/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(17685192422989999/100000000000000),(17727514058191/20000000000000),(-143654711271/50000000000000),(158106649/20000000000000)⟩
def e386 : ℝ := (25077497/50000000000000)
theorem h386 : Model (fun x => f386 ((83/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(5005226677176071/25000000000000),(17727514058191/20000000000000),(-143654711271/50000000000000),(158106649/20000000000000)⟩
def e387 : ℝ := (10030999/20000000000000)
theorem h387 : Model (fun x => f387 ((83/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(4661175912209267/20000000000000),(163393553384587/100000000000000),(-364487847621/100000000000000),(204130501/100000000000000)⟩
def e388 : ℝ := (12431837/12500000000000)
theorem h388 : Model (fun x => f388 ((83/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(23708260513427287/100000000000000),(163393553384587/100000000000000),(-364487847621/100000000000000),(204130501/100000000000000)⟩
def e389 : ℝ := (99454697/100000000000000)
theorem h389 : Model (fun x => f389 ((83/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(1103929751368601/4000000000000),(130752473125567/50000000000000),(-17758177391/6250000000000),(-774508783/50000000000000)⟩
def e390 : ℝ := (167022581/100000000000000)
theorem h390 : Model (fun x => f390 ((83/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(27580624736595977/100000000000000),(130752473125567/50000000000000),(-17758177391/6250000000000),(-774508783/50000000000000)⟩
def e391 : ℝ := (83511291/50000000000000)
theorem h391 : Model (fun x => f391 ((83/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(16052987201874869/50000000000000),(193680126781731/50000000000000),(47109655423/100000000000000),(-564884301/12500000000000)⟩
def e392 : ℝ := (126018157/50000000000000)
theorem h392 : Model (fun x => f392 ((83/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(32109307737083071/100000000000000),(193680126781731/50000000000000),(47109655423/100000000000000),(-564884301/12500000000000)⟩
def e393 : ℝ := (50407263/20000000000000)
theorem h393 : Model (fun x => f393 ((83/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(5268402962886631/100000000000000),(80062616345847/50000000000000),(174251036081/25000000000000),(-1997618369/50000000000000)⟩
def e394 : ℝ := (6316463/6250000000000)
theorem h394 : Model (fun x => f394 ((83/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(135507555756303/100000000000000),(70018899971/10000000000000),(-2544710051/100000000000000),(8079863/100000000000000)⟩
def e395 : ℝ := (388553/100000000000000)
theorem h395 : Model (fun x => f395 ((83/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(27050964087277/12500000000000),(300748542979/100000000000000),(-1481519923/100000000000000),(3649063/50000000000000)⟩
def e396 : ℝ := (138157/100000000000000)
theorem h396 : Model (fun x => f396 ((83/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(93664596230547/20000000000000),(325421521417/25000000000000),(-5507749897/100000000000000),(4535223/20000000000000)⟩
def e397 : ℝ := (664867/100000000000000)
theorem h397 : Model (fun x => f397 ((83/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1013487051552731/100000000000000),(4225423626757/100000000000000),(-14942691907/100000000000000),(23701223/50000000000000)⟩
def e398 : ℝ := (1167599/50000000000000)
theorem h398 : Model (fun x => f398 ((83/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1096632073378927/50000000000000),(121921901633/1000000000000),(-17322125183/50000000000000),(6900769/10000000000000)⟩
def e399 : ℝ := (1428157/20000000000000)
theorem h399 : Model (fun x => f399 ((83/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1486019318275451/50000000000000),(3187833317363/10000000000000),(-8694707861/50000000000000),(-282107747/100000000000000)⟩
def e400 : ℝ := (20650441/100000000000000)
theorem h400 : Model (fun x => f400 ((83/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(14550964087277/1562500000000),(300748542979/12500000000000),(-1481519923/12500000000000),(3649063/6250000000000)⟩
def e401 : ℝ := (138157/12500000000000)
theorem h401 : Model (fun x => f401 ((83/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1066769257342031/100000000000000),(1553088671771/50000000000000),(-2879373887/20000000000000),(66464871/100000000000000)⟩
def e402 : ℝ := (1493809/100000000000000)
theorem h402 : Model (fun x => f402 ((83/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1166769257342031/100000000000000),(1553088671771/50000000000000),(-2879373887/20000000000000),(66464871/100000000000000)⟩
def e403 : ℝ := (1493809/100000000000000)
theorem h403 : Model (fun x => f403 ((83/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(34676833127603183/100000000000000),(464263381992839/100000000000000),(1797113419/500000000000),(-1611453229/25000000000000)⟩
def e404 : ℝ := (150709187/50000000000000)
theorem h404 : Model (fun x => f404 ((83/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(288376968081/100000000000000),(-482609189/12500000000000),(12175369/25000000000000),(-69801/12500000000000)⟩
def e405 : ℝ := (8931/100000000000000)
theorem h405 : Model (fun x => f405 ((83/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (17106101787847627/50000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(7596430365331/50000000000000),(258357916669/100000000000000),(-200805409/12500000000000),(10132377/100000000000000)⟩
def e406 : ℝ := (1186591/100000000000000)
theorem h406 : Model (fun x => f406 ((83/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(16557376712071/50000000000000),(123627632791/20000000000000),(-2731551063/100000000000000),(7019423/50000000000000)⟩
def e407 : ℝ := (1977901/100000000000000)
theorem h407 : Model (fun x => f407 ((83/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(209424554825279/100000000000000),(66420738991/1562500000000),(-1032162061/12500000000000),(58164083/50000000000000)⟩
def e408 : ℝ := (7012321/50000000000000)
theorem h408 : Model (fun x => f408 ((83/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(50463748150669/50000000000000),(832645729103/100000000000000),(-11209037/80000000000),(56218141/25000000000000)⟩
def e409 : ℝ := (1736103/12500000000000)
theorem h409 : Model (fun x => f409 ((83/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-1303796918417/50000000000000),(79013914331/100000000000000),(549227597/100000000000000),(-21084013/100000000000000)⟩
def e410 : ℝ := (48761687/50000000000000)
theorem h410 : Model (fun x => f410 ((83/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(5700560041992187/100000000000000),(80267950439453/25000000000000),(737123/10240000),(8217/10240000)⟩
def e411 : ℝ := (445312501/100000000000000)
theorem h411 : Model (fun x => f411 ((83/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(41209/1600),(203/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((83/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(8365427/64000),(123627/64000),(609/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((83/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(745119045162540233/100000000000000),(52978841494919001/100000000000000),(807679946895843/50000000000000),(5507608258081/20000000000000)⟩
def e414 : ℝ := (11538738347/4000000000000)
theorem h414 : Model (fun x => f414 ((83/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(13420674273/100000000000000),(-59639109/6250000000000),(96879/250000000000),(-591299/50000000000000)⟩
def e415 : ℝ := (11357/25000000000000)
theorem h415 : Model (fun x => f415 ((83/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (345248508632040233/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5716645566657/100000000000000),(3522967719/100000000000000),(-51848249/6250000000000),(4534127/25000000000000)⟩
def e416 : ℝ := (9408649/25000000000000)
theorem h416 : Model (fun x => f416 ((83/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(3109051729823/100000000000000),(1650737641/2000000000000),(-280344387/100000000000000),(-589501/20000000000000)⟩
def e417 : ℝ := (13515797/10000000000000)
theorem h417 : Model (fun x => f417 ((83/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((83/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((777205780931/500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (41/20) (21/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (41/20) (21/10) ≤ (194318339979/125000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(83/40)-(1/40)) (by norm_num : ((83/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel21

