import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel28
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(97/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((97/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (97/40) (1/40)

def c3 : Certificate := ⟨(21247619047619/5000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((97/40)+(1/40)*x)) := (SharedCertificates.h2 (97/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((97/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-333523809523809/100000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((97/40)+(1/40)*x)) := (SharedCertificates.h4 (97/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(9409/1600),(97/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((97/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(711897883597883/100000000000000),(7339153439153/50000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((97/40)+(1/40)*x)) := (SharedCertificates.h8 (97/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((97/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((97/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(912673/64000),(28227/64000),(291/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((97/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(1736679923683449/12500000000000),(429694001736111/100000000000000),(1107458767361/25000000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((97/40)+(1/40)*x)) := (SharedCertificates.h13 (97/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((97/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((97/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(88529281/2560000),(912673/640000),(28227/1280000),(97/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((97/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(9660933442460317/100000000000000),(398389007936507/100000000000000),(385040922619/6250000000000),(42341269841/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((97/40)+(1/40)*x)) := (SharedCertificates.h18 (97/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((97/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(4193037234863281/50000000000000),(108067969970703/25000000000000),(912673/10240000),(9409/10240000),(14831543/3125000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((97/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(27316861096757449/50000000000000),(2816171247088393/100000000000000),(11613077307581/20000000000000),(598612232349/100000000000000),(772998049/25000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((97/40)+(1/40)*x)) := (SharedCertificates.h22 (97/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((97/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(317753602954483/1562500000000),(1257911170458983/100000000000000),(3242039099121/10000000000000),(445641113281/100000000000000),(1729956057/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((97/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(45665059587346483/100000000000000),(112985714442919/4000000000000),(4550004608687/6250000000000),(1000688298817/100000000000000),(485577613/6250000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((97/40)+(1/40)*x)) := (SharedCertificates.h26 (97/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((97/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(49315359178535761/100000000000000),(1779420176545103/50000000000000),(55033613707579/50000000000000),(945594737243/50000000000000),(9808906257/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((97/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(5851306505707219/50000000000000),(844518464741247/100000000000000),(26119127775501/100000000000000),(448782264183/100000000000000),(1163834513/25000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((97/40)+(1/40)*x)) := (SharedCertificates.h30 (97/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((97/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((97/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((97/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((97/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((97/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (97/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((97/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((97/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (97/40) (1/40))

def c43 : Certificate := ⟨(18769/1600),(137/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((97/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((97/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(20296892799/50000000000000),(-592610009/100000000000000),(648843/10000000000000),(-15787/25000000000000),(591/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((97/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-207901808702521/20000000000000),(13404839089/10000000000000),(-49678783/5000000000000),(7369847/100000000000000),(30138279/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((97/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((97/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (97/40) (1/40))

def c52 : Certificate := ⟨(73749999999999/50000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((97/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (97/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((97/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (97/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((97/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (97/40) (1/40))

def c56 : Certificate := ⟨(22346368715083/100000000000000),(-41613349563/100000000000000),(77492271/100000000000000),(-72153/50000000000000),(17/6250000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((97/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(10614525139663/100000000000000),(166453398249/100000000000000),(-61993817/20000000000000),(577223/100000000000000),(1339/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((97/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((97/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((97/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((97/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((97/40)+(1/40)*x)) := (SharedCertificates.h61 (97/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-31072688118343/20000000000000),(-1271183214561/50000000000000),(76799603/2500000000000),(-2624907/100000000000000),(9449/25000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((97/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((97/40)+(1/40)*x)) := (SharedCertificates.h61 (97/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-33018888682947/20000000000000),(-2858815425749/100000000000000),(457683517/50000000000000),(1868717/50000000000000),(5353/10000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((97/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((97/40)+(1/40)*x)) := (SharedCertificates.h67 (97/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-380270375488427/50000000000000),(-12229992870877/100000000000000),(17548144123/100000000000000),(-30576759/100000000000000),(114877/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((97/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((97/40)+(1/40)*x)) := (SharedCertificates.h67 (97/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-82374454898623/10000000000000),(-7107919735179/50000000000000),(5560690587/100000000000000),(763099/4000000000000),(58509/20000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((97/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((97/40)+(1/40)*x)) := (SharedCertificates.h72 (97/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(256772141856467/25000000000000),(14597512167071/100000000000000),(-3316619217/6250000000000),(111199221/100000000000000),(228863/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((97/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((97/40)+(1/40)*x)) := (SharedCertificates.h72 (97/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(611772856930319/25000000000000),(20736687238391/50000000000000),(-17065049987/50000000000000),(-110475011/100000000000000),(306857/25000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((97/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((97/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((97/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(122355731718731/100000000000000),(368243272103/100000000000000),(-204337163/50000000000000),(61269/25000000000000),(183/3125000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((97/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5741833220320453/50000000000000),(6588263010643/50000000000000),(-62893318437/100000000000000),(700607/500000000000),(1122543/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((97/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(870802025789/100000000000000),(-24979273/2500000000000),(5915639/100000000000000),(-11443/50000000000000),(159/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((97/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(4261864345101/20000000000000),(13468014367/4000000000000),(-113366881/20000000000000),(1272373/100000000000000),(6267/25000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((97/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((97/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((97/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (97/40) (1/40))

def c87 : Certificate := ⟨(9216589861751/50000000000000),(-2123638217/2500000000000),(391454049/100000000000000),(-56373/3125000000000),(4177/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((97/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(8755760368663/100000000000000),(56630352453/50000000000000),(-521938733/100000000000000),(2405247/100000000000000),(19073/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((97/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((97/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((97/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((97/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((97/40)+(1/40)*x)) := (SharedCertificates.h61 (97/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-127180445539289/100000000000000),(-852325949823/50000000000000),(3542929741/50000000000000),(-29106813/100000000000000),(336511/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((97/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((97/40)+(1/40)*x)) := (SharedCertificates.h61 (97/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-133716260208501/100000000000000),(-939475286629/50000000000000),(3330333193/50000000000000),(-5589563/25000000000000),(43273/10000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((97/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((97/40)+(1/40)*x)) := (SharedCertificates.h67 (97/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-124922220224841/20000000000000),(-8244213731947/100000000000000),(35688707587/100000000000000),(-156190243/100000000000000),(376229/25000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((97/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((97/40)+(1/40)*x)) := (SharedCertificates.h67 (97/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-667592677056913/100000000000000),(-2994410201/32000000000),(6716632341/20000000000000),(-113615347/100000000000000),(43049/2000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((97/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((97/40)+(1/40)*x)) := (SharedCertificates.h72 (97/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(860902023667769/100000000000000),(2579232693881/25000000000000),(-58977087609/100000000000000),(313422903/100000000000000),(1299241/50000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((97/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((97/40)+(1/40)*x)) := (SharedCertificates.h72 (97/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(198946671382187/10000000000000),(27541526903583/100000000000000),(-21110324809/20000000000000),(18005439/5000000000000),(1656669/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((97/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((97/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((97/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(5913907706683/5000000000000),(123177540819/50000000000000),(-1006997003/100000000000000),(2024693/50000000000000),(4973/10000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((97/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(35411907033969/312500000000),(9536325740777/100000000000000),(-60953629951/100000000000000),(344011941/100000000000000),(8804451/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((97/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(441235768099/50000000000000),(-742647101/100000000000000),(5371777/100000000000000),(-17653/50000000000000),(193/25000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((97/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(17556477471611/100000000000000),(114135709341/50000000000000),(-514564837/50000000000000),(4738801/100000000000000),(23057/25000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((97/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((97/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-404013497487471/100000000000000),(-727604218211/12500000000000),(4240341347/25000000000000),(-33687567/50000000000000),(13169433/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((97/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(41237113402061/100000000000000),(-212562440217/50000000000000),(2191365363/50000000000000),(-45182791/100000000000000),(3677/781250000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((97/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-83301752059271/50000000000000),(-170695478631/25000000000000),(14033366289/100000000000000),(-1077859/625000000000),(5543359/50000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((97/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((97/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((97/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((97/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((97/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((97/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((97/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((97/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((97/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((97/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (97/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((97/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((97/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(3059998543/100000000000000),(-126185507/100000000000000),(3252203/100000000000000),(-4191/6250000000000),(171/12500000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((97/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(57290630323909/50000000000000),(-21530077327/5000000000000),(756575979/20000000000000),(-7924159/25000000000000),(100709789/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((97/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((97/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (97/40) (1/40))

def c134 : Certificate := ⟨(38409/1600),(197/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((97/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((97/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(4866180048661/100000000000000),(-35519562399/100000000000000),(129633439/50000000000000),(-1892459/100000000000000),(13917/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((97/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(116815693430637/100000000000000),(86406885467/25000000000000),(518533737/100000000000000),(-3784919/100000000000000),(160671/25000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((97/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((97/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (97/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((97/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (97/40) (1/40))

def c140 : Certificate := ⟨(11995709563733/50000000000000),(-3978782637/20000000000000),(-834373/6250000000000),(126837/50000000000000),(37431/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((97/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(4034323490133/100000000000000),(621684787/781250000000),(53399869/100000000000000),(-1014697/100000000000000),(81153/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((97/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((97/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(16275766023/10000000000000),(6420678501/100000000000000),(16907873/25000000000000),(1557/50000000000000),(467/3125000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((97/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((97/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((97/40)+(1/40)*x)) := (SharedCertificates.h144 (97/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(969979790861/50000000000000),(76271049189/100000000000000),(795728539/100000000000000),(-37037/50000000000000),(178751/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((97/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((97/40)+(1/40)*x)) := (SharedCertificates.h148 (97/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-141181756093379/25000000000000),(-11135970626687/100000000000000),(-1845537569/25000000000000),(142708841/100000000000000),(22727589/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((97/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((97/40)+(1/40)*x)) := (SharedCertificates.h151 (97/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-115239349223667/10000000000000),(-23179829060749/100000000000000),(-24412867949/100000000000000),(17736361/6250000000000),(76061/160000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((97/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((97/40)+(1/40)*x)) := (SharedCertificates.h154 (97/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(1506723262345137/100000000000000),(5756890474211/20000000000000),(102635721/20000000000000),(-199660533/50000000000000),(31529579/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((97/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((97/40)+(1/40)*x)) := (SharedCertificates.h157 (97/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(2148412877571869/50000000000000),(85914678167247/100000000000000),(19950142461/25000000000000),(-216210241/20000000000000),(35223507/20000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((97/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((97/40)+(1/40)*x)) := (SharedCertificates.h160 (97/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(2291367683089673/50000000000000),(19465008348303/20000000000000),(203832019263/100000000000000),(-3190929/312500000000),(202520877/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((97/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(6764462790031/6250000000000),(165571983973/100000000000000),(17443123/10000000000000),(-50657/2500000000000),(84889/25000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((97/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((97/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((97/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((97/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((97/40)+(1/40)*x)) := (SharedCertificates.h167 (97/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(11353199728436983/20000000000000),(21162852506681/25000000000000),(65080719247/100000000000000),(-44104841/4000000000000),(183205027/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((97/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(88080895599/50000000000000),(-65674631/25000000000000),(9489/5000000000000),(3439/100000000000000),(73/12500000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((97/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(322921148277/4000000000000),(3188215173/2000000000000),(112099803/100000000000000),(-248993/12500000000000),(391053/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((97/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((97/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((97/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (97/40) (1/40))

def c175 : Certificate := ⟨(2775020762017/12500000000000),(-5110248799/10000000000000),(320041/781250000000),(320899/50000000000000),(4919/5000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((97/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(1866555935909/50000000000000),(17034162663/25000000000000),(-13655083/25000000000000),(-213933/25000000000000),(82129/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((97/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((97/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(5574449699/4000000000000),(5087234789/100000000000000),(8469591/20000000000000),(-34581/25000000000000),(6813/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((97/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((97/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((97/40)+(1/40)*x)) := (SharedCertificates.h144 (97/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(415482471881/25000000000000),(6047708097/10000000000000),(498233363/100000000000000),(-1699327/100000000000000),(163313/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((97/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((97/40)+(1/40)*x)) := (SharedCertificates.h148 (97/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-130643405088147/25000000000000),(-953574103083/10000000000000),(3852872697/50000000000000),(120031267/100000000000000),(5750413/25000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((97/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((97/40)+(1/40)*x)) := (SharedCertificates.h151 (97/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-266194895492353/25000000000000),(-19790306225147/100000000000000),(9369453949/100000000000000),(259016581/100000000000000),(47899959/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((97/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((97/40)+(1/40)*x)) := (SharedCertificates.h154 (97/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(279499731533347/20000000000000),(24768311085879/100000000000000),(-2098870081/6250000000000),(-293482219/100000000000000),(63684637/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((97/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((97/40)+(1/40)*x)) := (SharedCertificates.h157 (97/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(1985968826853377/50000000000000),(18355080181109/25000000000000),(-42492020101/100000000000000),(-957843593/100000000000000),(177622019/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((97/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((97/40)+(1/40)*x)) := (SharedCertificates.h160 (97/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1054080304398093/25000000000000),(10304737396203/12500000000000),(17594712959/50000000000000),(-588060877/50000000000000),(201781819/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((97/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(107605584986111/100000000000000),(141360536093/100000000000000),(-66892709/100000000000000),(-462447/25000000000000),(171071/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((97/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((97/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((97/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((97/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((97/40)+(1/40)*x)) := (SharedCertificates.h167 (97/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(56445694566442397/100000000000000),(72427869024381/100000000000000),(-201987269/390625000000),(-941225693/100000000000000),(184204969/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((97/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(177161430589/100000000000000),(-1420771/625000000000),(226991/50000000000000),(2163/100000000000000),(147/25000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((97/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(3734847493657/50000000000000),(17057934807/12500000000000),(-105917173/100000000000000),(-13267/781250000000),(387839/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((97/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((97/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(8904524373933/50000000000000),(136044611103/50000000000000),(-42437021/6250000000000),(2011237/100000000000000),(16924681/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((97/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1468787525597/20000000000000),(456138049/1250000000000),(-656193169/100000000000000),(3797127/50000000000000),(7298697/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((97/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((97/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((97/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((97/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((97/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((97/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (97/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((97/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((97/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((97/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (97/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((97/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(36068375721/100000000000000),(-70689161/100000000000000),(837631/50000000000000),(-787/12500000000000),(87/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((97/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(428509210616599/100000000000000),(-786229625029/50000000000000),(-6839647111/100000000000000),(-13400571/25000000000000),(2221269/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((97/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((97/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((97/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((97/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (97/40) (1/40))

def c223 : Certificate := ⟨(31329/1600),(177/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((97/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3535446321/2560000),(17145813/640000),(233867/1280000),(317/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((97/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((97/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(94718833063/100000000000000),(-86422293/6250000000000),(15139671/100000000000000),(-29469/20000000000000),(43/3125000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((97/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(65404951148827/50000000000000),(313957724937/50000000000000),(292457267/25000000000000),(-3617697/100000000000000),(3860631/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((97/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((97/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (97/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((97/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (97/40) (1/40))

def c231 : Certificate := ⟨(2321209412009/10000000000000),(-33832166913/100000000000000),(-6859687/50000000000000),(153393/50000000000000),(104659/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((97/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(7151623519639/100000000000000),(66078451/48828125000),(10975499/20000000000000),(-306787/25000000000000),(966243/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((97/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((97/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(255728594833/50000000000000),(1209774603/6250000000000),(95493873/50000000000000),(-26993/100000000000000),(36029/25000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((97/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((97/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((97/40)+(1/40)*x)) := (SharedCertificates.h144 (97/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(6064331290653/100000000000000),(228123834573/100000000000000),(2211584653/100000000000000),(-84567/10000000000000),(859889/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((97/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((97/40)+(1/40)*x)) := (SharedCertificates.h148 (97/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-1000793594606569/100000000000000),(-591296629193/3125000000000),(-7212640193/100000000000000),(174783919/100000000000000),(135345729/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((97/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((97/40)+(1/40)*x)) := (SharedCertificates.h151 (97/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-518506893898461/25000000000000),(-20299790730331/50000000000000),(-10509233283/25000000000000),(69647627/20000000000000),(5814573/2000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((97/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((97/40)+(1/40)*x)) := (SharedCertificates.h154 (97/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(2605048411161047/100000000000000),(46391253943161/100000000000000),(-37959534663/100000000000000),(-501263967/100000000000000),(18724433/5000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((97/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((97/40)+(1/40)*x)) := (SharedCertificates.h157 (97/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(307820318019661/4000000000000),(1163579735663/781250000000),(119116897919/100000000000000),(-691116743/50000000000000),(133591571/12500000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((97/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((97/40)+(1/40)*x)) := (SharedCertificates.h160 (97/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1076239026088379/12500000000000),(184226557350321/100000000000000),(486217337949/100000000000000),(-1189214479/100000000000000),(664588913/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((97/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(7175919014309/6250000000000),(18125858059/6250000000000),(18796421/6250000000000),(-2481289/100000000000000),(1038301/50000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((97/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((97/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((97/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((97/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((97/40)+(1/40)*x)) := (SharedCertificates.h167 (97/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(60092742881430203/100000000000000),(72394706903813/50000000000000),(70648675113/100000000000000),(-148172933/10000000000000),(1139258521/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((97/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(83204722571/50000000000000),(-400952343/100000000000000),(385213/50000000000000),(1359/50000000000000),(319/10000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((97/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(7163853566861/50000000000000),(272048747159/100000000000000),(68391939/50000000000000),(-2275119/100000000000000),(1255647/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((97/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((97/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((97/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (97/40) (1/40))

def c259 : Certificate := ⟨(20307466954209/100000000000000),(-77684421167/100000000000000),(7622301/5000000000000),(104513/25000000000000),(121431/25000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((97/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(156417768193/2500000000000),(103579228221/100000000000000),(-101630681/50000000000000),(-111481/20000000000000),(94693/10000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((97/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((97/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(391464291303/100000000000000),(12961305367/100000000000000),(40925807/50000000000000),(-61353/12500000000000),(24241/20000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((97/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((97/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((97/40)+(1/40)*x)) := (SharedCertificates.h144 (97/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(4648585919017/100000000000000),(153102810253/100000000000000),(946717881/100000000000000),(-5940977/100000000000000),(5659/390625000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((97/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((97/40)+(1/40)*x)) := (SharedCertificates.h148 (97/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-437824326653459/50000000000000),(-14486697781569/100000000000000),(28664958009/100000000000000),(78308483/100000000000000),(5305149/4000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((97/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((97/40)+(1/40)*x)) := (SharedCertificates.h151 (97/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-180666580699019/10000000000000),(-6163112958619/20000000000000),(9096262097/20000000000000),(112495323/50000000000000),(282109391/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((97/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((97/40)+(1/40)*x)) := (SharedCertificates.h154 (97/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(459159155362439/20000000000000),(18039315808727/50000000000000),(-103656260997/100000000000000),(-80708139/100000000000000),(366009057/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((97/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((97/40)+(1/40)*x)) := (SharedCertificates.h157 (97/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(6713187564760351/100000000000000),(56696746397013/50000000000000),(-37441280017/20000000000000),(-783822079/100000000000000),(6498209/625000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((97/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((97/40)+(1/40)*x)) := (SharedCertificates.h160 (97/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(7409595717178651/100000000000000),(17106816378203/12500000000000),(-3654597439/12500000000000),(-803490851/50000000000000),(1257959909/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((97/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(112904885746743/100000000000000),(220119761809/100000000000000),(-32467111/10000000000000),(-802817/50000000000000),(403013/20000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((97/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((97/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((97/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((97/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((97/40)+(1/40)*x)) := (SharedCertificates.h167 (97/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(11827168117825413/20000000000000),(55340874603029/50000000000000),(-104074804729/50000000000000),(-141982903/20000000000000),(549593787/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((97/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(42275546861/25000000000000),(-79125137/25000000000000),(593797/50000000000000),(-1307/100000000000000),(79/2500000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((97/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(6264894219253/50000000000000),(207972594531/100000000000000),(-394589461/100000000000000),(-548237/50000000000000),(2372673/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((97/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((97/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(57543421133971/50000000000000),(1634612488607/100000000000000),(-10489818579/100000000000000),(-900339/1562500000000),(4359931/20000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((97/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(23729245828441/50000000000000),(5775131407/3125000000000),(-3115448187/50000000000000),(1011863/2500000000000),(10588179/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((97/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((97/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((97/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((97/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((97/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((97/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (97/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((97/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(268447307975938249/25000000000000),(4208964651491/200000000000),(-45749615777077/100000000000000),0,(27781/20000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((97/40)+(1/40)*x)) := (SharedCertificates.h297 (97/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(4656407283/50000000000000),(-18251863/100000000000000),(8651/2000000000000),(-813/50000000000000),(3/12500000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((97/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(324246738460791/50000000000000),(634846149671/50000000000000),(4567340041/50000000000000),(4518711/12500000000000),(2867653/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((97/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((97/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (97/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((97/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (97/40) (1/40))

def c307 : Certificate := ⟨(3264400126834439/100000000000000),(11091229182759/50000000000000),0,0,(43/4000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((97/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (97/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((97/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (97/40) (1/40))

def c311 : Certificate := ⟨(1080299936582651/50000000000000),(2817541634481/100000000000000),0,0,(537/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((97/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (97/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(289271515639/6250000000000),(-1508904169/25000000000000),(7870777/100000000000000),(-1283/12500000000000),(9/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((97/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(75543837787323/50000000000000),(207413464473/25000000000000),(-540957251/50000000000000),(1410873/100000000000000),(2921/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((97/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((97/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (97/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((97/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (97/40) (1/40))

def c316 : Certificate := ⟨(11084319680493/50000000000000),(-40773220299/100000000000000),(32040463/25000000000000),(-8057/2000000000000),(663/50000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((97/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(11325442556053/100000000000000),(20386610149/12500000000000),(-512647409/100000000000000),(322279/20000000000000),(6651/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((97/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((97/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(160332061363/12500000000000),(4617747643/12500000000000),(149873703/100000000000000),(-326797/25000000000000),(1179/12500000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((97/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((97/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((97/40)+(1/40)*x)) := (SharedCertificates.h144 (97/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(1510134484271/10000000000000),(430752245167/100000000000000),(1657188243/100000000000000),(-15541607/100000000000000),(23177/20000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((97/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((97/40)+(1/40)*x)) := (SharedCertificates.h148 (97/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-395962915928017/25000000000000),(-2844948693799/12500000000000),(18145857689/25000000000000),(-113308799/50000000000000),(970489/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((97/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((97/40)+(1/40)*x)) := (SharedCertificates.h151 (97/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-83762553151041/2500000000000),(-50826780286439/100000000000000),(61380986723/50000000000000),(-133661649/50000000000000),(3191419/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((97/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((97/40)+(1/40)*x)) := (SharedCertificates.h154 (97/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(124401130951757/3125000000000),(51569971002727/100000000000000),(-249184513731/100000000000000),(249224979/25000000000000),(4595543/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((97/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((97/40)+(1/40)*x)) := (SharedCertificates.h157 (97/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(6171280999928169/50000000000000),(36716102626447/20000000000000),(-25140086523/5000000000000),(1198240749/100000000000000),(11523197/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((97/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((97/40)+(1/40)*x)) := (SharedCertificates.h160 (97/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(14687414222333561/100000000000000),(126544908163173/50000000000000),(-179902974003/100000000000000),(-1161157407/100000000000000),(26306293/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((97/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(12393354160301/10000000000000),(45390967941/12500000000000),(-175084223/20000000000000),(957801/50000000000000),(11367/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((97/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((97/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((97/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((97/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((97/40)+(1/40)*x)) := (SharedCertificates.h167 (97/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(64564372232610111/100000000000000),(87376545701123/50000000000000),(-556824528703/100000000000000),(1438702239/100000000000000),(17229257/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((97/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(38721045579/25000000000000),(-419217113/100000000000000),(1235223/50000000000000),(-6877/50000000000000),(7/6250000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((97/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(181987851373/800000000000),(41302992333/12500000000000),(-195358487/20000000000000),(127523/4000000000000),(45991/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((97/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((97/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((97/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (97/40) (1/40))

def c344 : Certificate := ⟨(4518646428993/25000000000000),(-2541001473/3125000000000),(471833499/100000000000000),(-684483/25000000000000),(16089/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((97/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(9233885712037/100000000000000),(54208031423/50000000000000),(-629111333/100000000000000),(146023/4000000000000),(37889/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((97/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((97/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(852646453429/100000000000000),(20022030673/100000000000000),(1357583/100000000000000),(-43121/6250000000000),(9501/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((97/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((97/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((97/40)+(1/40)*x)) := (SharedCertificates.h144 (97/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(10074292643073/100000000000000),(234717933787/100000000000000),(-4161431/25000000000000),(-1991273/25000000000000),(11/4882812500)⟩
theorem h350 : c350.Valid (fun x => f350 ((97/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((97/40)+(1/40)*x)) := (SharedCertificates.h148 (97/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1291813751016223/100000000000000),(-7572826530623/50000000000000),(44132571499/50000000000000),(-256471451/50000000000000),(532187/10000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((97/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((97/40)+(1/40)*x)) := (SharedCertificates.h151 (97/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-2704772604751577/100000000000000),(-33155563499053/100000000000000),(35201620327/20000000000000),(-925707579/100000000000000),(13272139/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((97/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((97/40)+(1/40)*x)) := (SharedCertificates.h154 (97/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1652645194020499/50000000000000),(2234139336751/6250000000000),(-61221350457/25000000000000),(202582413/12500000000000),(9074323/50000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((97/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((97/40)+(1/40)*x)) := (SharedCertificates.h157 (97/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(20001573469043/200000000000),(120721097660693/100000000000000),(-332609319841/50000000000000),(3613036991/100000000000000),(47366841/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((97/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((97/40)+(1/40)*x)) := (SharedCertificates.h160 (97/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(5771251216189697/50000000000000),(4931758775853/3125000000000),(-647488000753/100000000000000),(2269175673/100000000000000),(81417219/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((97/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((97/40)+(1/40)*x)) := (SharedCertificates.h41 (97/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(119320417877503/100000000000000),(47370831273/20000000000000),(-1256865083/100000000000000),(3305607/50000000000000),(4739/5000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((97/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((97/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((97/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((97/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((97/40)+(1/40)*x)) := (SharedCertificates.h167 (97/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(62322744272645579/100000000000000),(14523351729247/12500000000000),(-671926943623/100000000000000),(3790706427/100000000000000),(56773187/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((97/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(40113766317/25000000000000),(-299132573/100000000000000),(2287597/100000000000000),(-69/400000000000),(9/4000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((97/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(9260264905717/50000000000000),(21869683189/10000000000000),(-1246961257/100000000000000),(7196973/100000000000000),(206201/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((97/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((97/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(133813422918211/50000000000000),(127656307347/3125000000000),(-3678961349/100000000000000),(104190573/100000000000000),(816039/25000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((97/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(27590396477981/25000000000000),(273394265423/50000000000000),(-1788523157/25000000000000),(29179679/25000000000000),(5095087/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((97/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((97/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(5922124754394531/50000000000000),(143719259033203/25000000000000),(1138489/10240000),(10961/10240000),(128417969/25000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((97/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(47089/1600),(217/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((97/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(10218313/64000),(141267/64000),(651/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((97/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(1891066386420357601/100000000000000),(29482324558888621/25000000000000),(1582262057806487/50000000000000),(23831893038879/50000000000000),(22138096617/5000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((97/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(5288021653/100000000000000),(-329767737/100000000000000),(292893/2500000000000),(-62411/20000000000000),(2597/25000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((97/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5643560051837/100000000000000),(-11657044359/100000000000000),(-328122681/100000000000000),(1492269/20000000000000),(10623943/50000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((97/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((97/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((97/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel28

namespace Hf4Quad.Panel29
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(99/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((99/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (99/40) (1/40)

def c3 : Certificate := ⟨(86742857142857/20000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((99/40)+(1/40)*x)) := (SharedCertificates.h2 (99/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((99/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-171142857142857/50000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((99/40)+(1/40)*x)) := (SharedCertificates.h4 (99/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(9801/1600),(99/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((99/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(370778571428571/50000000000000),(1872619047619/12500000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((99/40)+(1/40)*x)) := (SharedCertificates.h8 (99/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((99/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((99/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(970299/64000),(29403/64000),(297/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((99/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(189064557/1280000),(5729229/1280000),(57871/1280000),(608912037/4000000000000),(1/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((99/40)+(1/40)*x)) := (SharedCertificates.h13 (99/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((99/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((99/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(96059601/2560000),(970299/640000),(29403/1280000),(99/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((99/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(2620673638392857/25000000000000),(211771607142857/50000000000000),(6417321428571/100000000000000),(21607142857/50000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((99/40)+(1/40)*x)) := (SharedCertificates.h18 (99/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((99/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(9287012206054687/100000000000000),(117260255126953/25000000000000),(970299/10240000),(9801/10240000),(484375001/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((99/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(6050316470537109/10000000000000),(381964423645019/12500000000000),(61731624023437/100000000000000),(155887939453/25000000000000),(631122687/20000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((99/40)+(1/40)*x)) := (SharedCertificates.h22 (99/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((99/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(459707104199707/2000000000000),(1393051830908201/100000000000000),(7035615307617/20000000000000),(473778808593/100000000000000),(3603759771/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((99/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(51613675931840119/100000000000000),(3128101571626669/100000000000000),(19748115982491/25000000000000),(531935784039/50000000000000),(4046126051/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((99/40)+(1/40)*x)) := (SharedCertificates.h26 (99/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((99/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(56888754144713741/100000000000000),(4022437161747431/100000000000000),(24378407040893/20000000000000),(2052054464719/100000000000000),(5213467411/25000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((99/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(3374947914537581/25000000000000),(954530723303557/100000000000000),(180782333959/625000000000),(486955781707/100000000000000),(4948656369/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((99/40)+(1/40)*x)) := (SharedCertificates.h30 (99/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((99/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((99/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((99/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((99/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((99/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (99/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((99/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((99/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (99/40) (1/40))

def c43 : Certificate := ⟨(19321/1600),(139/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((99/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((99/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(19717011591/50000000000000),(-283698009/50000000000000),(3061489/50000000000000),(-29367/50000000000000),(271/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((99/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1039244863095041/100000000000000),(26032134493/20000000000000),(-950678271/100000000000000),(3476439/50000000000000),(28436207/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((99/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((99/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (99/40) (1/40))

def c52 : Certificate := ⟨(29833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((99/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (99/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((99/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (99/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((99/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (99/40) (1/40))

def c56 : Certificate := ⟨(22263450834879/100000000000000),(-4130510359/10000000000000),(15326569/20000000000000),(-4443/3125000000000),(133/50000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((99/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(10946196660481/100000000000000),(82610207179/50000000000000),(-153265691/50000000000000),(568703/100000000000000),(1323/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((99/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((99/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((99/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((99/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((99/40)+(1/40)*x)) := (SharedCertificates.h61 (99/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-16043590652653/10000000000000),(-2530110018759/100000000000000),(3056214563/100000000000000),(-263143/10000000000000),(37223/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((99/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((99/40)+(1/40)*x)) := (SharedCertificates.h61 (99/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-85404191544577/50000000000000),(-571021897787/20000000000000),(937506749/100000000000000),(113837/3125000000000),(52947/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((99/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((99/40)+(1/40)*x)) := (SharedCertificates.h67 (99/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-784930787759197/100000000000000),(-12160165222889/100000000000000),(17366175641/100000000000000),(-30081097/100000000000000),(113891/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((99/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((99/40)+(1/40)*x)) := (SharedCertificates.h67 (99/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-170430766782091/20000000000000),(-14193370504557/100000000000000),(5673116301/100000000000000),(9200659/50000000000000),(144047/50000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((99/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((99/40)+(1/40)*x)) := (SharedCertificates.h72 (99/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(1056072214840837/100000000000000),(1798322145507/12500000000000),(-52403031279/100000000000000),(27440529/25000000000000),(227573/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((99/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((99/40)+(1/40)*x)) := (SharedCertificates.h72 (99/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(3952969971449/156250000000),(20667773425959/50000000000000),(-17389564323/50000000000000),(-52945373/50000000000000),(1507/125000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((99/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((99/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((99/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(123090585534261/100000000000000),(366611531673/100000000000000),(-407191967/100000000000000),(249003/100000000000000),(1153/20000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((99/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(11509769036970037/100000000000000),(12926627382971/100000000000000),(-62057703989/100000000000000),(34604599/25000000000000),(552533/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((99/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(868827164809/100000000000000),(-39031209/4000000000000),(5780391/100000000000000),(-11101/50000000000000),(153/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((99/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(10990232617181/50000000000000),(334448188231/100000000000000),(-559276453/100000000000000),(1247027/100000000000000),(1229/5000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((99/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((99/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((99/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (99/40) (1/40))

def c87 : Certificate := ⟨(2283105022831/12500000000000),(-3336043869/4000000000000),(15233077/4000000000000),(-217367/12500000000000),(399/5000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((99/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(8980213089801/100000000000000),(55600731149/50000000000000),(-101553847/20000000000000),(115929/5000000000000),(3697/20000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((99/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((99/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((99/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((99/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((99/40)+(1/40)*x)) := (SharedCertificates.h61 (99/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-32640409221377/25000000000000),(-1676654011453/100000000000000),(864251061/12500000000000),(-704573/2500000000000),(325511/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((99/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((99/40)+(1/40)*x)) := (SharedCertificates.h61 (99/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-27489539292613/20000000000000),(-1852574024597/100000000000000),(6528150031/100000000000000),(-21816171/100000000000000),(418459/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((99/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((99/40)+(1/40)*x)) := (SharedCertificates.h67 (99/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-640958012315477/100000000000000),(-8103311304277/100000000000000),(4345989493/12500000000000),(-1206243/800000000000),(729187/50000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((99/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((99/40)+(1/40)*x)) := (SharedCertificates.h67 (99/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-686174311608153/100000000000000),(-4612275832863/50000000000000),(32909666319/100000000000000),(-110893571/100000000000000),(10401/500000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((99/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((99/40)+(1/40)*x)) := (SharedCertificates.h72 (99/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(881302459079217/100000000000000),(10084733276707/100000000000000),(-57134065803/100000000000000),(150509193/50000000000000),(1255279/50000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((99/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((99/40)+(1/40)*x)) := (SharedCertificates.h72 (99/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(2044130426440149/100000000000000),(27123610601681/100000000000000),(-51707142413/50000000000000),(35235121/10000000000000),(3195497/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((99/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((99/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((99/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(14845858556373/12500000000000),(121187590571/50000000000000),(-983078337/100000000000000),(3924293/100000000000000),(12023/25000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((99/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(1135064181132021/10000000000000),(464829114517/5000000000000),(-1178643761/2000000000000),(329918647/100000000000000),(4244317/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((99/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(881007450171/100000000000000),(-144315333/20000000000000),(5165161/100000000000000),(-6717/20000000000000),(369/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((99/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(18008941348149/100000000000000),(56052765499/25000000000000),(-250305643/25000000000000),(456491/10000000000000),(88689/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((99/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((99/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-51948481711367/12500000000000),(-5753787079667/100000000000000),(16564389993/100000000000000),(-64962051/100000000000000),(6384739/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((99/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(1010101010101/2500000000000),(-408121620243/100000000000000),(128826269/3125000000000),(-8328163/20000000000000),(424909/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((99/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-167914284319569/100000000000000),(-125731714883/20000000000000),(13042769437/100000000000000),(-39498109/25000000000000),(10355931/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((99/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((99/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((99/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((99/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((99/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((99/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((99/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((99/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((99/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((99/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (99/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((99/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((99/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(564023727/20000000000000),(-28486047/25000000000000),(1438689/50000000000000),(-58129/100000000000000),(1161/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((99/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(22746987935167/20000000000000),(-10396056159/2500000000000),(3598677649/100000000000000),(-3718589/12500000000000),(92045793/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((99/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((99/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (99/40) (1/40))

def c134 : Certificate := ⟨(39201/1600),(199/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((99/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((99/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(599520383693/12500000000000),(-6900954057/20000000000000),(248235757/100000000000000),(-1785869/100000000000000),(12943/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((99/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(58754496402873/50000000000000),(69531425217/20000000000000),(496471503/100000000000000),(-111617/3125000000000),(122109/20000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((99/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((99/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (99/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((99/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (99/40) (1/40))

def c140 : Certificate := ⟨(23951579899627/100000000000000),(-797773229/4000000000000),(-742123/6250000000000),(119253/50000000000000),(35443/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((99/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(262105025093/6250000000000),(79777322899/100000000000000),(47495869/100000000000000),(-238507/25000000000000),(38543/25000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((99/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((99/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(87934776549/50000000000000),(669121191/10000000000000),(33813931/50000000000000),(-1059/25000000000000),(14679/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((99/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((99/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((99/40)+(1/40)*x)) := (SharedCertificates.h144 (99/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(419136764643/20000000000000),(9931589849/12500000000000),(15900379/2000000000000),(-161381/100000000000000),(175577/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((99/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((99/40)+(1/40)*x)) := (SharedCertificates.h148 (99/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-587027369926549/100000000000000),(-11163821332313/100000000000000),(-6551700491/100000000000000),(6710457/5000000000000),(10794497/50000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((99/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((99/40)+(1/40)*x)) := (SharedCertificates.h151 (99/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-1198848564180621/100000000000000),(-23274140119403/100000000000000),(-22758612243/100000000000000),(133913711/50000000000000),(22611807/50000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((99/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((99/40)+(1/40)*x)) := (SharedCertificates.h154 (99/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(1564291077293317/100000000000000),(7195454243299/25000000000000),(-361080671/20000000000000),(-37384207/10000000000000),(59901729/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((99/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((99/40)+(1/40)*x)) := (SharedCertificates.h157 (99/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(178758631595723/4000000000000),(86221156005359/100000000000000),(73499286307/100000000000000),(-204020209/20000000000000),(167470431/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((99/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((99/40)+(1/40)*x)) := (SharedCertificates.h160 (99/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(2389096353261149/50000000000000),(98128311023513/100000000000000),(197850321121/100000000000000),(-38935393/4000000000000),(193445537/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((99/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(54281615178037/50000000000000),(41561464427/25000000000000),(406549/250000000000),(-478073/25000000000000),(323023/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((99/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((99/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((99/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((99/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((99/40)+(1/40)*x)) := (SharedCertificates.h167 (99/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(1779236034109413/3125000000000),(2653086100877/3125000000000),(5865420143/10000000000000),(-1040287877/100000000000000),(43612707/25000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((99/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(175637180233/100000000000000),(-261899239/100000000000000),(52397/25000000000000),(1583/50000000000000),(69/12500000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((99/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(4196141467917/50000000000000),(31967149631/20000000000000),(100515943/100000000000000),(-467713/25000000000000),(186633/50000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((99/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((99/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((99/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (99/40) (1/40))

def c175 : Certificate := ⟨(11049065002683/50000000000000),(-509311449/1000000000000),(44652477/100000000000000),(587971/100000000000000),(2893/3125000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((99/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(3869159992843/100000000000000),(33954096599/50000000000000),(-29768319/50000000000000),(-391981/50000000000000),(155851/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((99/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((99/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(74851995251/50000000000000),(2627476643/50000000000000),(41508091/100000000000000),(-70763/50000000000000),(1663/12500000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((99/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((99/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((99/40)+(1/40)*x)) := (SharedCertificates.h144 (99/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(1784863312207/100000000000000),(62449471781/100000000000000),(60990779/12500000000000),(-1735131/100000000000000),(159447/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((99/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((99/40)+(1/40)*x)) := (SharedCertificates.h148 (99/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-270806669890409/50000000000000),(-2375879677329/25000000000000),(4197676813/50000000000000),(109967713/100000000000000),(21824699/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((99/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((99/40)+(1/40)*x)) := (SharedCertificates.h151 (99/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-1104320684654741/100000000000000),(-9874900136209/50000000000000),(10863878831/100000000000000),(119684719/50000000000000),(22750399/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((99/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((99/40)+(1/40)*x)) := (SharedCertificates.h154 (99/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1446898663121203/100000000000000),(12315289393181/50000000000000),(-17627760947/50000000000000),(-264770499/100000000000000),(6041491/10000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((99/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((99/40)+(1/40)*x)) := (SharedCertificates.h157 (99/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(823720163339123/20000000000000),(73239162097839/100000000000000),(-600160203/1250000000000),(-883353237/100000000000000),(33733591/20000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((99/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((99/40)+(1/40)*x)) := (SharedCertificates.h160 (99/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(4381328502614133/100000000000000),(41282409187589/50000000000000),(5667555043/20000000000000),(-1108510873/100000000000000),(192283823/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((99/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(26972005994047/25000000000000),(70535669841/50000000000000),(-15513037/20000000000000),(-34189/2000000000000),(162503/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((99/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((99/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((99/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((99/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((99/40)+(1/40)*x)) := (SharedCertificates.h167 (99/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(452722688753531/800000000000),(72210047106929/100000000000000),(-57126724933/100000000000000),(-432859553/50000000000000),(43777269/25000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((99/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(88354308263/50000000000000),(-1803861/800000000000),(233051/50000000000000),(47/2500000000000),(557/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((99/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(1935546245607/25000000000000),(13602001377/10000000000000),(-11567257/10000000000000),(-777763/50000000000000),(369271/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((99/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((99/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(4587631838463/25000000000000),(269397438523/100000000000000),(-666904137/100000000000000),(2013137/100000000000000),(16045511/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((99/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1853588621601/25000000000000),(8488745087/25000000000000),(-612435817/100000000000000),(874951/12500000000000),(3388281/50000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((99/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((99/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((99/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((99/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((99/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((99/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (99/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((99/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((99/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((99/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (99/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((99/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(17966824707/50000000000000),(-4003813/6250000000000),(1639467/100000000000000),(-2821/50000000000000),(41/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((99/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(21266825088731/5000000000000),(-1600467042679/100000000000000),(-7165823951/100000000000000),(-55160113/100000000000000),(1062803/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((99/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((99/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((99/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((99/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (99/40) (1/40))

def c223 : Certificate := ⟨(32041/1600),(179/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((99/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3674493921/2560000),(17617359/640000),(237683/1280000),(319/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((99/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((99/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(46006360379/50000000000000),(-33098101/2500000000000),(285739/2000000000000),(-68523/50000000000000),(63/5000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((99/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(66035192007801/50000000000000),(316276113241/50000000000000),(1148769349/100000000000000),(-3406887/100000000000000),(919439/25000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((99/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((99/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (99/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((99/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (99/40) (1/40))

def c231 : Certificate := ⟨(11572188664103/50000000000000),(-33883431847/100000000000000),(-2385959/20000000000000),(290047/100000000000000),(99123/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((99/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(296899627487/4000000000000),(135533727383/100000000000000),(47719179/100000000000000),(-1160189/100000000000000),(460067/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((99/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((99/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(550933680011/100000000000000),(4023991317/20000000000000),(38155563/20000000000000),(-42879/100000000000000),(17777/12500000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((99/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((99/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((99/40)+(1/40)*x)) := (SharedCertificates.h144 (99/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(6529418157949/100000000000000),(59239818327/25000000000000),(275743549/12500000000000),(-515869/50000000000000),(848393/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((99/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((99/40)+(1/40)*x)) := (SharedCertificates.h148 (99/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-5193320253749/500000000000),(-18948283989821/100000000000000),(-3096336613/50000000000000),(41344251/25000000000000),(128892249/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((99/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((99/40)+(1/40)*x)) := (SharedCertificates.h151 (99/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-2155392134846939/100000000000000),(-40763618384733/100000000000000),(-19998989119/50000000000000),(41467919/12500000000000),(277551979/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((99/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((99/40)+(1/40)*x)) := (SharedCertificates.h154 (99/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1348837567040629/50000000000000),(23116762982007/50000000000000),(-40873949139/100000000000000),(-235352669/50000000000000),(35667623/10000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((99/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((99/40)+(1/40)*x)) := (SharedCertificates.h157 (99/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(7993849907131167/100000000000000),(74699176286543/50000000000000),(111020602347/100000000000000),(-10295081/781250000000),(1019540693/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((99/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((99/40)+(1/40)*x)) := (SharedCertificates.h160 (99/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(4490150375670433/50000000000000),(37231459369257/20000000000000),(119796409141/25000000000000),(-231156939/20000000000000),(1277052207/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((99/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(115395915054361/100000000000000),(291187411351/100000000000000),(286216173/100000000000000),(-2363257/100000000000000),(495621/25000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((99/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((99/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((99/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((99/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((99/40)+(1/40)*x)) := (SharedCertificates.h167 (99/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(60382592590701247/100000000000000),(29010901167409/20000000000000),(619647549/1000000000000),(-1414151117/100000000000000),(544667353/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((99/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(165610643249/100000000000000),(-12432479/3125000000000),(392881/50000000000000),(2399/100000000000000),(151/5000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((99/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(1487233383999/10000000000000),(1362845643/500000000000),(123539267/100000000000000),(-2142301/100000000000000),(24097/1000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((99/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((99/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((99/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (99/40) (1/40))

def c259 : Certificate := ⟨(2015271111653/10000000000000),(-3082794629/4000000000000),(77386103/50000000000000),(89617/25000000000000),(91119/20000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((99/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(3231525922313/50000000000000),(20551964193/20000000000000),(-206362943/100000000000000),(-238979/50000000000000),(5623/625000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((99/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((99/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(417710391463/100000000000000),(830177563/6250000000000),(493257/625000000000),(-242949/50000000000000),(118707/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((99/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((99/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((99/40)+(1/40)*x)) := (SharedCertificates.h144 (99/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(2479265509617/50000000000000),(156818661393/100000000000000),(182255433/20000000000000),(-5871353/100000000000000),(1418597/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((99/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((99/40)+(1/40)*x)) := (SharedCertificates.h148 (99/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-56531674113571/6250000000000),(-2874228857223/20000000000000),(1455031117/5000000000000),(33561881/50000000000000),(126013829/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((99/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((99/40)+(1/40)*x)) := (SharedCertificates.h151 (99/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-934056629500401/50000000000000),(-153155169649/500000000000),(5845152129/12500000000000),(202050109/100000000000000),(33566201/12500000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((99/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((99/40)+(1/40)*x)) := (SharedCertificates.h154 (99/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(473507566347091/20000000000000),(8915790406931/25000000000000),(-52024416741/50000000000000),(-793181/1562500000000),(69547129/20000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((99/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((99/40)+(1/40)*x)) := (SharedCertificates.h157 (99/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(867402454295437/12500000000000),(28158904568963/25000000000000),(-191644139909/100000000000000),(-696968559/100000000000000),(123640869/12500000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((99/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((99/40)+(1/40)*x)) := (SharedCertificates.h160 (99/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(7683175162020059/100000000000000),(17089833520987/12500000000000),(-38604846741/100000000000000),(-1517022593/100000000000000),(15039639/1250000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((99/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(22668762816143/20000000000000),(109401241469/50000000000000),(-166902383/50000000000000),(-720907/50000000000000),(1918067/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((99/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((99/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((99/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((99/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((99/40)+(1/40)*x)) := (SharedCertificates.h167 (99/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(11871273198436849/20000000000000),(109840993155151/100000000000000),(-26517579359/12500000000000),(-24880061/4000000000000),(1047484763/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((99/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(168473925801/100000000000000),(-1217839/390625000000),(1179063/100000000000000),(-1531/100000000000000),(299/10000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((99/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(6472073410811/50000000000000),(206381719453/100000000000000),(-400693021/100000000000000),(-941061/100000000000000),(566703/25000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((99/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((99/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(59156822881457/50000000000000),(795979588453/50000000000000),(-1083756659/10000000000000),(-58343287/100000000000000),(20762911/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((99/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(2390174661877/5000000000000),(40088065249/25000000000000),(-5998534593/100000000000000),(9254553/25000000000000),(4928947/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((99/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((99/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((99/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((99/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((99/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((99/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (99/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((99/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(269453799523033923/25000000000000),(384296772527439/20000000000000),(-45749615777077/100000000000000),0,(69701/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((99/40)+(1/40)*x)) := (SharedCertificates.h297 (99/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9278028383/100000000000000),(-8270241/50000000000000),(105827/25000000000000),(-1457/100000000000000),(3/12500000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((99/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(651069695165741/100000000000000),(1306675777707/100000000000000),(1169945703/12500000000000),(38759953/100000000000000),(2808121/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((99/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((99/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (99/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((99/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (99/40) (1/40))

def c307 : Certificate := ⟨(3308765043565477/100000000000000),(11091229182759/50000000000000),0,0,(1077/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((99/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (99/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((99/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (99/40) (1/40))

def c311 : Certificate := ⟨(270779369554283/12500000000000),(2817541634481/100000000000000),0,0,(1077/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((99/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (99/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2308152209043/50000000000000),(-3002128153/50000000000000),(7809513/100000000000000),(-5079/50000000000000),(9/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((99/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(76371333445099/50000000000000),(206335767947/25000000000000),(-53674661/5000000000000),(1396237/100000000000000),(1453/50000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((99/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((99/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (99/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((99/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (99/40) (1/40))

def c316 : Certificate := ⟨(22087602365131/100000000000000),(-251658543/625000000000),(7860927/6250000000000),(-98219/25000000000000),(643/50000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((99/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(728099408717/6250000000000),(161061467519/100000000000000),(-50309933/10000000000000),(1571501/100000000000000),(203/3125000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((99/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((99/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(1357129597373/100000000000000),(7505200593/20000000000000),(142189939/100000000000000),(-313613/25000000000000),(4573/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((99/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((99/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((99/40)+(1/40)*x)) := (SharedCertificates.h144 (99/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(3992338771527/25000000000000),(218598579253/50000000000000),(782962867/50000000000000),(-7442121/50000000000000),(56071/50000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((99/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((99/40)+(1/40)*x)) := (SharedCertificates.h148 (99/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-325816462209351/20000000000000),(-22471953296189/100000000000000),(71240144577/100000000000000),(-27646321/12500000000000),(946759/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((99/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((99/40)+(1/40)*x)) := (SharedCertificates.h151 (99/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-138066670793603/4000000000000),(-12584731331953/25000000000000),(4846769679/4000000000000),(-131795061/50000000000000),(3108007/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((99/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((99/40)+(1/40)*x)) := (SharedCertificates.h154 (99/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(4082987312223331/100000000000000),(395195946553/781250000000),(-121644410487/50000000000000),(242122373/25000000000000),(4475567/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((99/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((99/40)+(1/40)*x)) := (SharedCertificates.h157 (99/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(12707721370098211/100000000000000),(181583615007689/100000000000000),(-123916213931/25000000000000),(590363773/50000000000000),(2241091/20000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((99/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((99/40)+(1/40)*x)) := (SharedCertificates.h160 (99/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(3038573015894489/20000000000000),(50471304243819/20000000000000),(-23335325089/12500000000000),(-1099162247/100000000000000),(12833937/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((99/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(124656310676317/100000000000000),(359648938003/100000000000000),(-864008721/100000000000000),(37771/2000000000000),(11069/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((99/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((99/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((99/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((99/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((99/40)+(1/40)*x)) := (SharedCertificates.h167 (99/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(811395782295053/1250000000000),(10783935690549/6250000000000),(-109651463471/20000000000000),(283408661/20000000000000),(16721341/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((99/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(77027760513/50000000000000),(-409498021/100000000000000),(2389679/100000000000000),(-6587/50000000000000),(107/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((99/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(11702723728479/50000000000000),(326554671773/100000000000000),(-239482277/25000000000000),(193759/6250000000000),(17877/20000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((99/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((99/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((99/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (99/40) (1/40))

def c344 : Certificate := ⟨(3582765460703/20000000000000),(-79457067201/100000000000000),(11394499/2500000000000),(-1307217/50000000000000),(1899/12500000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((99/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(4724115130989/50000000000000),(105942756267/100000000000000),(-121541323/20000000000000),(3485911/100000000000000),(18139/50000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((99/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((99/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(892690550833/100000000000000),(4003886223/20000000000000),(-519273/20000000000000),(-628929/100000000000000),(18057/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((99/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((99/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((99/40)+(1/40)*x)) := (SharedCertificates.h144 (99/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(1317949961557/12500000000000),(234558727533/100000000000000),(-12446831/20000000000000),(-181043/2500000000000),(107039/50000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((99/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((99/40)+(1/40)*x)) := (SharedCertificates.h148 (99/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-330439013275019/25000000000000),(-739932702429/5000000000000),(85257469901/100000000000000),(-61229447/12500000000000),(5096563/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((99/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((99/40)+(1/40)*x)) := (SharedCertificates.h151 (99/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-173149189297023/6250000000000),(-8115621864681/25000000000000),(170567471251/100000000000000),(-4440773/500000000000),(396519/3125000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((99/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((99/40)+(1/40)*x)) := (SharedCertificates.h154 (99/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(675163221047407/20000000000000),(6957161244281/20000000000000),(-235407268071/100000000000000),(1539568181/100000000000000),(1081667/6250000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((99/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((99/40)+(1/40)*x)) := (SharedCertificates.h157 (99/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(1279949581740079/12500000000000),(118102969779027/100000000000000),(-160998945593/25000000000000),(3462553847/100000000000000),(22637383/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((99/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((99/40)+(1/40)*x)) := (SharedCertificates.h160 (99/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(11855563114597331/100000000000000),(155253396993837/100000000000000),(-633994684139/100000000000000),(2228420239/100000000000000),(7774433/10000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((99/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((99/40)+(1/40)*x)) := (SharedCertificates.h41 (99/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(119789151074789/100000000000000),(231904943649/100000000000000),(-243601919/20000000000000),(6342893/100000000000000),(90613/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((99/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((99/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((99/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((99/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((99/40)+(1/40)*x)) := (SharedCertificates.h167 (99/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(15638115047001349/25000000000000),(113543935883743/100000000000000),(-649674528917/100000000000000),(3628206013/100000000000000),(846897/1562500000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((99/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(159865814549/100000000000000),(-290185131/100000000000000),(546779/25000000000000),(-16257/100000000000000),(211/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((99/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(18952992542521/100000000000000),(53448506591/25000000000000),(-602384061/50000000000000),(6870453/100000000000000),(39117/20000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((99/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((99/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(275782966181571/100000000000000),(101788352427/2500000000000),(-9548421/312500000000),(103648497/100000000000000),(1600609/50000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((99/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(111427461083461/100000000000000),(259767185857/50000000000000),(-324118263/5000000000000),(21471323/20000000000000),(296609/6250000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((99/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((99/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(13039340370117187/100000000000000),(155162559814453/25000000000000),(1205523/10240000),(2277/2048000),(523437501/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((99/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(47961/1600),(219/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((99/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(10503459/64000),(143883/64000),(657/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((99/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(2139971515071417169/100000000000000),(65586826186392109/50000000000000),(865319472499191/25000000000000),(51288869780639/100000000000000),(46892102121/10000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((99/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(1168239849/25000000000000),(-71609499/25000000000000),(1249941/12500000000000),(-261641/100000000000000),(8549/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((99/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(1404747850749/25000000000000),(-12883502509/100000000000000),(-11438323/4000000000000),(6611441/100000000000000),(9835573/50000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((99/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((99/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((99/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel29

namespace Hf4Quad.Panel30
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(101/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((101/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (101/40) (1/40)

def c3 : Certificate := ⟨(44247619047619/10000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((101/40)+(1/40)*x)) := (SharedCertificates.h2 (101/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((101/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-351047619047619/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((101/40)+(1/40)*x)) := (SharedCertificates.h4 (101/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(10201/1600),(101/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((101/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(771821693121693/100000000000000),(15283597883597/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((101/40)+(1/40)*x)) := (SharedCertificates.h8 (101/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((101/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((101/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1030301/64000),(30603/64000),(303/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((101/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(15684067016782407/100000000000000),(465863376736111/100000000000000),(922501736111/20000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((101/40)+(1/40)*x)) := (SharedCertificates.h13 (101/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((101/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((101/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(104060401/2560000),(1030301/640000),(30603/1280000),(101/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((101/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(11355797728174603/100000000000000),(449734563492063/100000000000000),(1669806547619/25000000000000),(44087301587/100000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((101/40)+(1/40)*x)) := (SharedCertificates.h18 (101/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((101/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(2565942505126953/25000000000000),(127026856689453/25000000000000),(1030301/10240000),(10201/10240000),(247070313/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((101/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(66866560985456449/100000000000000),(3310225791359227/100000000000000),(65549025571469/100000000000000),(324500126591/50000000000000),(3219234673/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((101/40)+(1/40)*x)) := (SharedCertificates.h22 (101/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((101/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(1036640772071289/4000000000000),(153956550307617/10000000000000),(7621611401367/20000000000000),(125769165039/25000000000000),(1875268557/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((101/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(5819448990304961/10000000000000),(3457098410082151/100000000000000),(85571742823813/100000000000000),(112965997127/10000000000000),(4210920507/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((101/40)+(1/40)*x)) := (SharedCertificates.h26 (101/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((101/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(32718974368500059/50000000000000),(1133825844452971/25000000000000),(67355990759581/50000000000000),(17366953063/781250000000),(22140786147/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((101/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(3882132276262507/25000000000000),(107623469044901/10000000000000),(31967367043039/100000000000000),(13187857691/2500000000000),(5254043699/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((101/40)+(1/40)*x)) := (SharedCertificates.h30 (101/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((101/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((101/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((101/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((101/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((101/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (101/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((101/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((101/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (101/40) (1/40))

def c43 : Certificate := ⟨(19881/1600),(141/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((101/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((101/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(38323261501/100000000000000),(-271796181/50000000000000),(5782897/100000000000000),(-10937/20000000000000),(31/6250000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((101/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-519494144921899/50000000000000),(63219795513/50000000000000),(-182043069/20000000000000),(3280989/50000000000000),(26806523/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((101/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((101/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (101/40) (1/40))

def c52 : Certificate := ⟨(150833333333331/100000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((101/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (101/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((101/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (101/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((101/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (101/40) (1/40))

def c56 : Certificate := ⟨(11090573012939/50000000000000),(-41000269919/100000000000000),(75786081/100000000000000),(-70043/50000000000000),(131/50000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((101/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(11275415896487/100000000000000),(164001079673/100000000000000),(-12125773/4000000000000),(28017/5000000000000),(653/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((101/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((101/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((101/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((101/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((101/40)+(1/40)*x)) := (SharedCertificates.h61 (101/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-20685490346143/12500000000000),(-2517916761117/100000000000000),(1520204351/50000000000000),(-2637009/100000000000000),(18321/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((101/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((101/40)+(1/40)*x)) := (SharedCertificates.h61 (101/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-176514823084861/100000000000000),(-178207257637/6250000000000),(959083723/100000000000000),(1774929/50000000000000),(52347/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((101/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((101/40)+(1/40)*x)) := (SharedCertificates.h67 (101/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-809181893175857/100000000000000),(-12091059544053/100000000000000),(2148393609/12500000000000),(-1849757/6250000000000),(112821/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((101/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((101/40)+(1/40)*x)) := (SharedCertificates.h67 (101/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-27516179267773/3125000000000),(-14170459868321/100000000000000),(2890773029/50000000000000),(2218177/12500000000000),(283631/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((101/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((101/40)+(1/40)*x)) := (SharedCertificates.h72 (101/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(271159158072669/25000000000000),(7089138243191/50000000000000),(-6468591049/12500000000000),(108341419/100000000000000),(3533/1562500000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((101/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((101/40)+(1/40)*x)) := (SharedCertificates.h72 (101/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(1306215960387559/50000000000000),(41195177587887/100000000000000),(-35401052707/100000000000000),(-101439631/100000000000000),(591969/50000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((101/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((101/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((101/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(123822181829361/100000000000000),(364985766961/100000000000000),(-101421669/25000000000000),(252721/100000000000000),(2837/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((101/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(28838437912199/250000000000),(6340025406663/50000000000000),(-61232272207/100000000000000),(34181821/25000000000000),(33987/3125000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((101/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(866898549641/100000000000000),(-119115303/12500000000000),(353073/6250000000000),(-2693/12500000000000),(149/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((101/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(11323567215779/50000000000000),(166112973723/50000000000000),(-55186863/10000000000000),(152791/12500000000000),(24141/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((101/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((101/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((101/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (101/40) (1/40))

def c87 : Certificate := ⟨(1131221719457/6250000000000),(-81898405029/100000000000000),(185290509/50000000000000),(-838419/50000000000000),(61/800000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((101/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(9200603318249/100000000000000),(109197873371/100000000000000),(-19764321/4000000000000),(1117891/50000000000000),(17917/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((101/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((101/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((101/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((101/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((101/40)+(1/40)*x)) := (SharedCertificates.h61 (101/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-133887512540673/100000000000000),(-412333146281/25000000000000),(6747592849/100000000000000),(-6823687/25000000000000),(39367/12500000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((101/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((101/40)+(1/40)*x)) := (SharedCertificates.h61 (101/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-5645076215081/4000000000000),(-913360546077/50000000000000),(6398844437/100000000000000),(-425759/2000000000000),(80951/20000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((101/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((101/40)+(1/40)*x)) := (SharedCertificates.h67 (101/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-657026759016491/100000000000000),(-497876754801/6250000000000),(33878872823/100000000000000),(-145605273/100000000000000),(353361/25000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((101/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((101/40)+(1/40)*x)) := (SharedCertificates.h67 (101/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-352246329034643/50000000000000),(-9094233027863/100000000000000),(32252311137/100000000000000),(-108235197/100000000000000),(2010921/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((101/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((101/40)+(1/40)*x)) := (SharedCertificates.h72 (101/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(901245773541001/100000000000000),(9859761397557/100000000000000),(-13840922431/25000000000000),(289202071/100000000000000),(121303/5000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((101/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((101/40)+(1/40)*x)) := (SharedCertificates.h72 (101/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1048983396962137/50000000000000),(5342830182729/20000000000000),(-101323228051/100000000000000),(43085373/12500000000000),(3082887/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((101/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((101/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((101/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(23849543530139/20000000000000),(238489473063/100000000000000),(-479948067/50000000000000),(3803863/100000000000000),(1163/2500000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((101/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(284225046481921/2500000000000),(9064758252131/100000000000000),(-28496621407/50000000000000),(3956331/1250000000000),(8186699/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((101/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(87958469211/10000000000000),(-140262491/20000000000000),(4968563/100000000000000),(-6393/20000000000000),(177/25000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((101/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(4613348691227/25000000000000),(55065069909/25000000000000),(-97433447/10000000000000),(879813/20000000000000),(85363/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((101/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((101/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-427029685415113/100000000000000),(-5688299861357/100000000000000),(1618152949/10000000000000),(-62667147/100000000000000),(1545177/12500000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((101/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(39603960396039/100000000000000),(-392118419763/100000000000000),(3882360591/100000000000000),(-19219607/50000000000000),(192197/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((101/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-42280166872783/25000000000000),(-144582492483/25000000000000),(12134565839/100000000000000),(-18120361/12500000000000),(1209643/12500000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((101/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((101/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((101/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((101/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((101/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((101/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((101/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((101/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((101/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((101/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (101/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((101/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((101/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(650822667/25000000000000),(-103100621/100000000000000),(510399/20000000000000),(-10107/20000000000000),(989/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((101/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(112917415773861/100000000000000),(-25112312889/6250000000000),(1712848417/50000000000000),(-5591683/20000000000000),(84304403/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((101/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((101/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (101/40) (1/40))

def c134 : Certificate := ⟨(40001/1600),(201/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((101/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((101/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(2364066193853/50000000000000),(-16766426907/50000000000000),(118910829/50000000000000),(-1686679/100000000000000),(241/2000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((101/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(3693945774231/3125000000000),(349600959027/100000000000000),(47564331/10000000000000),(-843343/25000000000000),(580489/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((101/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((101/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (101/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((101/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (101/40) (1/40))

def c140 : Certificate := ⟨(23911645621499/100000000000000),(-9994511017/50000000000000),(-5242907/50000000000000),(112189/50000000000000),(6717/20000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((101/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(4353417514003/100000000000000),(39978044067/50000000000000),(20971627/50000000000000),(-897513/100000000000000),(29313/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((101/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((101/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(2961288133/1562500000000),(435102793/6250000000000),(6758169/10000000000000),(-11073/100000000000000),(901/6250000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((101/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((101/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((101/40)+(1/40)*x)) := (SharedCertificates.h144 (101/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(2257767879907/100000000000000),(41315263939/50000000000000),(99225569/12500000000000),(-121211/50000000000000),(86213/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((101/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((101/40)+(1/40)*x)) := (SharedCertificates.h148 (101/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-609380161898111/100000000000000),(-2797112466003/25000000000000),(-1154096563/20000000000000),(25258071/20000000000000),(2052417/10000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((101/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((101/40)+(1/40)*x)) := (SharedCertificates.h151 (101/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-1245485766615773/100000000000000),(-5840505288191/25000000000000),(-21196765033/100000000000000),(1264821/500000000000),(43056749/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((101/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((101/40)+(1/40)*x)) := (SharedCertificates.h154 (101/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(1621844547392889/100000000000000),(3596275739231/12500000000000),(-3976386373/100000000000000),(-350098417/100000000000000),(7118573/12500000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((101/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((101/40)+(1/40)*x)) := (SharedCertificates.h157 (101/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(2320847027139627/50000000000000),(43251571589739/50000000000000),(33775546787/50000000000000),(-240824591/25000000000000),(159377173/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((101/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((101/40)+(1/40)*x)) := (SharedCertificates.h160 (101/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(4975233033514007/100000000000000),(98908212489277/100000000000000),(192144792829/100000000000000),(-37159767/4000000000000),(184923483/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((101/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(54448178734259/50000000000000),(41718455239/25000000000000),(75734099/50000000000000),(-1806099/100000000000000),(153773/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((101/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((101/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((101/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((101/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((101/40)+(1/40)*x)) := (SharedCertificates.h167 (101/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(28552788507583251/50000000000000),(85121125142597/100000000000000),(10517772461/20000000000000),(-982171503/100000000000000),(83125521/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((101/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(43778561231/25000000000000),(-3262799/1250000000000),(28477/12500000000000),(91/3125000000000),(523/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((101/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(8712341759847/100000000000000),(6408632847/4000000000000),(44816593/50000000000000),(-879069/50000000000000),(178299/50000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((101/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((101/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((101/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (101/40) (1/40))

def c175 : Certificate := ⟨(21996450927247/100000000000000),(-1014913651/2000000000000),(24014431/50000000000000),(53813/10000000000000),(87181/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((101/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(4004732097003/100000000000000),(33830455033/50000000000000),(-16009621/25000000000000),(-179377/25000000000000),(9249/6250000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((101/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((101/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(160378791687/100000000000000),(1083855273/20000000000000),(1270339/3125000000000),(-144127/100000000000000),(6493/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((101/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((101/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((101/40)+(1/40)*x)) := (SharedCertificates.h144 (101/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(1911700018349/100000000000000),(64380233879/100000000000000),(95485241/20000000000000),(-440937/25000000000000),(38907/25000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((101/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((101/40)+(1/40)*x)) := (SharedCertificates.h148 (101/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-560585935116187/100000000000000),(-236716391993/2500000000000),(2256710857/25000000000000),(25162143/25000000000000),(20723331/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((101/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((101/40)+(1/40)*x)) := (SharedCertificates.h151 (101/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-1143774952035723/100000000000000),(-19703546657043/100000000000000),(6122344273/50000000000000),(110563211/50000000000000),(43253463/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((101/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((101/40)+(1/40)*x)) := (SharedCertificates.h154 (101/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1496016734724499/100000000000000),(24486487576533/100000000000000),(-9190898053/25000000000000),(-238275663/100000000000000),(2294211/4000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((101/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((101/40)+(1/40)*x)) := (SharedCertificates.h157 (101/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(2132440082102599/50000000000000),(912959904177/1250000000000),(-26551468839/50000000000000),(-814215099/100000000000000),(40070729/25000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((101/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((101/40)+(1/40)*x)) := (SharedCertificates.h160 (101/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(4546562751522429/100000000000000),(41332562382203/50000000000000),(2187871857/10000000000000),(-1045202551/100000000000000),(9168041/5000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((101/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(108169842985693/100000000000000),(140741096497/100000000000000),(-2185653/2500000000000),(-1579143/100000000000000),(154477/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((101/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((101/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((101/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((101/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((101/40)+(1/40)*x)) := (SharedCertificates.h167 (101/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(28367260449518259/50000000000000),(14394287411073/20000000000000),(-62108264761/100000000000000),(-198918171/25000000000000),(166582843/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((101/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(176259530203/100000000000000),(-223596701/100000000000000),(476601/100000000000000),(811/50000000000000),(263/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((101/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(4006875073109/50000000000000),(13553919623/10000000000000),(-62302101/50000000000000),(-711731/50000000000000),(17587/5000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((101/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((101/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(18886670740289/100000000000000),(133376993069/50000000000000),(-654837973/100000000000000),(500813/25000000000000),(951507/6250000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((101/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(3739934800057/50000000000000),(7896757043/25000000000000),(-4576677/800000000000),(6457571/100000000000000),(314971/5000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((101/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((101/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((101/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((101/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((101/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((101/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (101/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((101/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((101/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((101/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (101/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((101/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(8953010349/25000000000000),(-57568323/100000000000000),(1607497/100000000000000),(-251/5000000000000),(79/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((101/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(422106459798009/100000000000000),(-407449745423/25000000000000),(-7501883731/100000000000000),(-11378643/20000000000000),(514937/25000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((101/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((101/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((101/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((101/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (101/40) (1/40))

def c223 : Certificate := ⟨(32761/1600),(181/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((101/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3817344481/2560000),(18096561/640000),(241523/1280000),(321/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((101/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((101/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(44710471751/50000000000000),(-634191089/50000000000000),(13493427/100000000000000),(-63799/50000000000000),(1157/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((101/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(33335014176091/25000000000000),(637107237523/100000000000000),(282233041/25000000000000),(-3209949/100000000000000),(1754523/50000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((101/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((101/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (101/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((101/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (101/40) (1/40))

def c231 : Certificate := ⟨(23076565033133/100000000000000),(-1696386749/5000000000000),(-1023739/10000000000000),(137189/50000000000000),(188049/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((101/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1538747973493/20000000000000),(33927734979/25000000000000),(20474779/50000000000000),(-1097513/100000000000000),(438791/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((101/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((101/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(295968165741/50000000000000),(20882493377/100000000000000),(190475697/100000000000000),(-28867/50000000000000),(28077/20000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((101/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((101/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((101/40)+(1/40)*x)) := (SharedCertificates.h144 (101/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(7012151894733/100000000000000),(245769986369/100000000000000),(549808627/25000000000000),(-1205027/100000000000000),(13083/781250000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((101/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((101/40)+(1/40)*x)) := (SharedCertificates.h148 (101/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-134573010589901/12500000000000),(-4742776606893/25000000000000),(-1045465307/20000000000000),(4892731/3125000000000),(122936693/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((101/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((101/40)+(1/40)*x)) := (SharedCertificates.h151 (101/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-89483069672921/4000000000000),(-10229923283839/25000000000000),(-1189211763/3125000000000),(316302539/100000000000000),(132690699/50000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((101/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((101/40)+(1/40)*x)) := (SharedCertificates.h154 (101/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(2789974983822599/100000000000000),(4606449925029/10000000000000),(-21805414439/50000000000000),(-442055731/100000000000000),(170118837/50000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((101/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((101/40)+(1/40)*x)) := (SharedCertificates.h157 (101/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(8293080278460909/100000000000000),(74913435464667/50000000000000),(12912347437/12500000000000),(-157167633/12500000000000),(60882037/6250000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((101/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((101/40)+(1/40)*x)) := (SharedCertificates.h160 (101/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(4677261454043949/50000000000000),(94030150350653/50000000000000),(118086745917/25000000000000),(-140601831/12500000000000),(245761227/20000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((101/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(28994854016603/25000000000000),(292304373209/100000000000000),(272374813/100000000000000),(-56319/2500000000000),(1895549/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((101/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((101/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((101/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((101/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((101/40)+(1/40)*x)) := (SharedCertificates.h167 (101/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(3792058642508369/6250000000000),(4540176759097/3125000000000),(5367369851/10000000000000),(-135070519/10000000000000),(1043210897/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((101/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(82409063113/50000000000000),(-3946687/1000000000000),(799257/100000000000000),(263/12500000000000),(573/20000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((101/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(3854487343623/25000000000000),(136519044919/50000000000000),(55532491/50000000000000),(-10091/500000000000),(1157869/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((101/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((101/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((101/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (101/40) (1/40))

def c259 : Certificate := ⟨(19999193228021/100000000000000),(-4777918789/6250000000000),(156755759/100000000000000),(303763/100000000000000),(428001/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((101/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(6667742362637/100000000000000),(20385786833/20000000000000),(-209007679/100000000000000),(-405019/100000000000000),(856059/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((101/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((101/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(88917576429/20000000000000),(6796358723/50000000000000),(76022889/100000000000000),(-48009/10000000000000),(1163/1000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((101/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((101/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((101/40)+(1/40)*x)) := (SharedCertificates.h144 (101/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(2637883318313/50000000000000),(160393627213/100000000000000),(219071317/25000000000000),(-45247/781250000000),(277917/20000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((101/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((101/40)+(1/40)*x)) := (SharedCertificates.h148 (101/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-233283039060549/25000000000000),(-1425397861657/10000000000000),(29471964261/100000000000000),(2274123/4000000000000),(23981389/20000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((101/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((101/40)+(1/40)*x)) := (SharedCertificates.h151 (101/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-1929186709619509/100000000000000),(-30441651797987/100000000000000),(47908654147/100000000000000),(45201967/25000000000000),(127989419/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((101/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((101/40)+(1/40)*x)) := (SharedCertificates.h154 (101/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1219223805061791/50000000000000),(550726082649/1562500000000),(-52135116821/50000000000000),(-2360477/10000000000000),(66173249/20000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((101/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((101/40)+(1/40)*x)) := (SharedCertificates.h157 (101/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(7163718885059769/100000000000000),(111861008296573/100000000000000),(-195580725767/100000000000000),(-616669397/100000000000000),(942489969/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((101/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((101/40)+(1/40)*x)) := (SharedCertificates.h160 (101/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1989111529611891/25000000000000),(136546393160413/100000000000000),(-23723839449/50000000000000),(-715918771/50000000000000),(1152392589/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((101/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(113780072607419/100000000000000),(13590661611/6250000000000),(-341992469/100000000000000),(-80633/6250000000000),(914209/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((101/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((101/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((101/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((101/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((101/40)+(1/40)*x)) := (SharedCertificates.h167 (101/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(59575194608135839/100000000000000),(108985300271381/100000000000000),(-215624849981/100000000000000),(-135218237/25000000000000),(124958289/12500000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((101/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(167855095829/100000000000000),(-61413943/20000000000000),(46771/4000000000000),(-1727/100000000000000),(1417/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((101/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(6677650128351/50000000000000),(20476824267/10000000000000),(-3171119/781250000000),(-19963/2500000000000),(2168761/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((101/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((101/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(30363436346769/25000000000000),(1547905265351/100000000000000),(-5595174887/50000000000000),(-59298789/100000000000000),(1238093/6250000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((101/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(48100493222603/100000000000000),(136789281103/100000000000000),(-1446542753/25000000000000),(4225519/12500000000000),(1839121/20000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((101/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((101/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((101/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((101/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((101/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((101/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (101/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((101/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(54073758367715089/5000000000000),(1738485399528891/100000000000000),(-45749615777077/100000000000000),0,(2797/2000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((101/40)+(1/40)*x)) := (SharedCertificates.h297 (101/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(577914333/6250000000000),(-14864077/100000000000000),(207527/50000000000000),(-81/6250000000000),(1/5000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((101/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(326860400422721/50000000000000),(1344590214017/100000000000000),(240005883/2500000000000),(20723793/50000000000000),(247053/10000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((101/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((101/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (101/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((101/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (101/40) (1/40))

def c307 : Certificate := ⟨(1676564980148257/50000000000000),(11091229182759/50000000000000),0,0,(27/2500000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((101/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (101/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((101/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (101/40) (1/40))

def c311 : Certificate := ⟨(2171870039703227/100000000000000),(2817541634481/100000000000000),0,0,(1079/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((101/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (101/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2302163531241/50000000000000),(-5973139719/100000000000000),(1937221/25000000000000),(-10053/100000000000000),(9/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((101/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(38597267550531/25000000000000),(821065796159/100000000000000),(-1065159081/100000000000000),(690901/50000000000000),(289/10000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((101/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((101/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (101/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((101/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (101/40) (1/40))

def c316 : Certificate := ⟨(4401514321439/20000000000000),(-9941735777/25000000000000),(61723361/50000000000000),(-38321/10000000000000),(1249/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((101/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(11969713571219/100000000000000),(159067772427/100000000000000),(-123446723/25000000000000),(383209/25000000000000),(6347/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((101/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((101/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(143274042977/10000000000000),(38079913487/100000000000000),(2106497/1562500000000),(-30099/2500000000000),(1109/12500000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((101/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((101/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((101/40)+(1/40)*x)) := (SharedCertificates.h144 (101/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(8424947652957/50000000000000),(221642396063/50000000000000),(184814899/12500000000000),(-3564013/25000000000000),(13571/12500000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((101/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((101/40)+(1/40)*x)) := (SharedCertificates.h148 (101/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-418435753941373/25000000000000),(-22189625466739/100000000000000),(34964530031/50000000000000),(-107941101/50000000000000),(184797/20000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((101/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((101/40)+(1/40)*x)) := (SharedCertificates.h151 (101/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-3551862044846733/100000000000000),(-24928698310893/50000000000000),(11959881863/10000000000000),(-259886237/100000000000000),(756963/25000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((101/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((101/40)+(1/40)*x)) := (SharedCertificates.h154 (101/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(2091596005853159/50000000000000),(24811718490141/50000000000000),(-237560738393/100000000000000),(941022467/100000000000000),(4359901/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((101/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((101/40)+(1/40)*x)) := (SharedCertificates.h157 (101/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(1306891535171531/10000000000000),(179615054668449/100000000000000),(-488632734559/100000000000000),(232664073/20000000000000),(340647/3125000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((101/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((101/40)+(1/40)*x)) := (SharedCertificates.h160 (101/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(15696822718710731/100000000000000),(251596841258241/100000000000000),(-96548981571/50000000000000),(-207945099/20000000000000),(25049993/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((101/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(7835760473263/6250000000000),(356215458341/100000000000000),(-106594747/12500000000000),(116357/6250000000000),(10783/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((101/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((101/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((101/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((101/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((101/40)+(1/40)*x)) := (SharedCertificates.h167 (101/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(8156820848709513/12500000000000),(34073372008073/20000000000000),(-5398197601/1000000000000),(1395483179/100000000000000),(8117471/50000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((101/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(15324597943/10000000000000),(-10002379/2500000000000),(23123/1000000000000),(-789/6250000000000),(101/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((101/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(24054749714679/100000000000000),(322759815629/100000000000000),(-469792009/50000000000000),(188459/6250000000000),(86667/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((101/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((101/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((101/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (101/40) (1/40))

def c344 : Certificate := ⟨(4439178902671/25000000000000),(-15532969497/20000000000000),(88089301/20000000000000),(-2497823/100000000000000),(7177/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((101/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(4828856259543/50000000000000),(103553129979/100000000000000),(-587262009/100000000000000),(3330429/100000000000000),(34749/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((101/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((101/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(932714111013/100000000000000),(4000345439/20000000000000),(-3099823/50000000000000),(-57297/10000000000000),(17171/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((101/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((101/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((101/40)+(1/40)*x)) := (SharedCertificates.h144 (101/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(5506205818611/50000000000000),(46845119681/20000000000000),(-51834071/50000000000000),(-6579331/100000000000000),(203661/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((101/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((101/40)+(1/40)*x)) := (SharedCertificates.h148 (101/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1351016205614699/100000000000000),(-451981677037/3125000000000),(82384545517/100000000000000),(-234005791/50000000000000),(488263/10000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((101/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((101/40)+(1/40)*x)) := (SharedCertificates.h151 (101/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-708659191642153/25000000000000),(-7947682718447/25000000000000),(33069302489/20000000000000),(-42623203/5000000000000),(3034133/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((101/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((101/40)+(1/40)*x)) := (SharedCertificates.h154 (101/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1722229124986299/50000000000000),(3386234255109/10000000000000),(-226400734673/100000000000000),(292679489/20000000000000),(3302459/20000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((101/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((101/40)+(1/40)*x)) := (SharedCertificates.h157 (101/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(5236627010331297/50000000000000),(28891989625607/25000000000000),(-155913180167/25000000000000),(829922671/25000000000000),(43296023/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((101/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((101/40)+(1/40)*x)) := (SharedCertificates.h160 (101/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(6081775837229359/50000000000000),(152743993568727/100000000000000),(-77593586323/12500000000000),(2186774139/100000000000000),(37138853/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((101/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((101/40)+(1/40)*x)) := (SharedCertificates.h41 (101/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(24049627829837/20000000000000),(227107987153/100000000000000),(-73795229/6250000000000),(380493/6250000000000),(86669/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((101/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((101/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((101/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((101/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((101/40)+(1/40)*x)) := (SharedCertificates.h167 (101/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(62776978074268501/100000000000000),(110988151762499/100000000000000),(-628371625829/100000000000000),(3474112379/100000000000000),(51773751/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((101/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(159294064587/100000000000000),(-56325597/20000000000000),(2092379/100000000000000),(-7667/50000000000000),(99/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((101/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(3875163172077/20000000000000),(104528075141/50000000000000),(-1164478051/100000000000000),(6562427/100000000000000),(185631/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((101/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((101/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(283914641089013/100000000000000),(4060554725991/100000000000000),(-1217254739/50000000000000),(103377373/100000000000000),(1508589/50000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((101/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(14055180251931/12500000000000),(247429440713/50000000000000),(-5863755057/100000000000000),(98998513/100000000000000),(1094889/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((101/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((101/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(1791078679321289/12500000000000),(167272989501953/25000000000000),(10201/81920),(11817/10240000),(266601563/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((101/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(48841/1600),(221/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((101/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(10793861/64000),(146523/64000),(663/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((101/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(96663271523287839/4000000000000),(145649365024932897/100000000000000),(3780416201312681/100000000000000),(55126785797973/100000000000000),(496198733131/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((101/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(1034519093/25000000000000),(-49881051/20000000000000),(2139599/25000000000000),(-220059/100000000000000),(7061/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((101/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5592131912763/100000000000000),(-1743884231/12500000000000),(-62144067/25000000000000),(2931829/50000000000000),(18232391/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((101/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((101/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((101/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel30
