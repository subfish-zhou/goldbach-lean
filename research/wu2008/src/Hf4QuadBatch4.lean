import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel13
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(67/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((67/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (67/40) (1/40)

def c3 : Certificate := ⟨(293523809523809/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((67/40)+(1/40)*x)) := (SharedCertificates.h2 (67/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((67/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-101047619047619/50000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((67/40)+(1/40)*x)) := (SharedCertificates.h4 (67/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(4489/1600),(67/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((67/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(67928783068783/20000000000000),(158416005291/1562500000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((67/40)+(1/40)*x)) := (SharedCertificates.h8 (67/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((67/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((67/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(300763/64000),(13467/64000),(201/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((67/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(4578455274884259/100000000000000),(51251365017361/25000000000000),(3059782986111/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((67/40)+(1/40)*x)) := (SharedCertificates.h13 (67/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((67/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((67/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(20151121/2560000),(300763/640000),(13467/1280000),(67/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((67/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(68719720672123/3125000000000),(4102669890873/3125000000000),(734806547619/25000000000000),(14623015873/50000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((67/40)+(1/40)*x)) := (SharedCertificates.h18 (67/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((67/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(1318481549804687/100000000000000),(24598536376953/25000000000000),(300763/10240000),(4489/10240000),(328125001/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((67/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(8589663133727571/100000000000000),(320509818422669/50000000000000),(2391864316587/12500000000000),(285595739293/100000000000000),(2137673621/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((67/40)+(1/40)*x)) := (SharedCertificates.h22 (67/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((67/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(44169131918457/2000000000000),(98886116235351/50000000000000),(1475912182617/20000000000000),(146856933593/100000000000000),(165375977/10000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((67/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(2479547564311263/50000000000000),(17763922848797/4000000000000),(828541177649/5000000000000),(329767632893/100000000000000),(3713521941/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((67/40)+(1/40)*x)) := (SharedCertificates.h26 (67/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((67/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(3699164798170773/100000000000000),(386479904286497/100000000000000),(270391724081/1562500000000),(86094877319/20000000000000),(6482814951/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((67/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(10972720978701/1250000000000),(91712294747351/100000000000000),(513315082541/12500000000000),(102152255231/100000000000000),(38459557/2500000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((67/40)+(1/40)*x)) := (SharedCertificates.h30 (67/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((67/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((67/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((67/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((67/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((67/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (67/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((67/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((67/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (67/40) (1/40))

def c43 : Certificate := ⟨(11449/1600),(107/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((67/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((67/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(6654771263/10000000000000),(-15548531/1250000000000),(4359401/25000000000000),(-54323/25000000000000),(261/10000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((67/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-261170085554069/25000000000000),(5541496811/2500000000000),(-1056130819/50000000000000),(20136683/100000000000000),(4084103/5000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((67/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((67/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (67/40) (1/40))

def c52 : Certificate := ⟨(61249999999999/50000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((67/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (67/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((67/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (67/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((67/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (67/40) (1/40))

def c56 : Certificate := ⟨(11834319526627/50000000000000),(-2334185311/5000000000000),(23019579/25000000000000),(-36323/20000000000000),(181/50000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((67/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(5325443786981/100000000000000),(186734824877/100000000000000),(-73662653/20000000000000),(145291/20000000000000),(1603/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((67/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((67/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((67/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((67/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((67/40)+(1/40)*x)) := (SharedCertificates.h61 (67/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-9532229263679/12500000000000),(-2733621045833/100000000000000),(3299563811/100000000000000),(-297673/12500000000000),(23977/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((67/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((67/40)+(1/40)*x)) := (SharedCertificates.h61 (67/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-39308640553201/50000000000000),(-2902264933403/100000000000000),(508347371/100000000000000),(1075711/20000000000000),(31423/50000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((67/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((67/40)+(1/40)*x)) := (SharedCertificates.h67 (67/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-75393556840169/20000000000000),(-2674560414233/20000000000000),(20679018837/100000000000000),(-39497849/100000000000000),(16239/12500000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((67/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((67/40)+(1/40)*x)) := (SharedCertificates.h67 (67/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-196428136265657/50000000000000),(-2897505786021/20000000000000),(3299921899/100000000000000),(16087473/50000000000000),(186497/50000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((67/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((67/40)+(1/40)*x)) := (SharedCertificates.h72 (67/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(13456256441893/2500000000000),(18102031930259/100000000000000),(-8012934669/12500000000000),(134658903/100000000000000),(240227/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((67/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((67/40)+(1/40)*x)) := (SharedCertificates.h72 (67/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(1175671625077611/100000000000000),(21576270822903/50000000000000),(-10266336951/50000000000000),(-24754149/12500000000000),(1621001/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((67/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((67/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((67/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(27733622772311/25000000000000),(393358566013/100000000000000),(-213578107/50000000000000),(30949/20000000000000),(373/5000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((67/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(220556147964417/2000000000000),(4338000162169/25000000000000),(-15337543897/20000000000000),(166640897/100000000000000),(1426403/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((67/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(906798571909/100000000000000),(-1426826643/100000000000000),(1068873/12500000000000),(-927/2500000000000),(13/5000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((67/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(10660973506543/100000000000000),(74906367081/20000000000000),(-701370463/100000000000000),(1751231/100000000000000),(16417/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((67/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((67/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((67/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (67/40) (1/40))

def c87 : Certificate := ⟨(21390374331551/100000000000000),(-114387028511/100000000000000),(611695339/100000000000000),(-3271099/100000000000000),(17589/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((67/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(2406417112299/50000000000000),(76258019007/50000000000000),(-815593787/100000000000000),(4361463/100000000000000),(31367/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((67/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((67/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((67/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((67/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((67/40)+(1/40)*x)) := (SharedCertificates.h61 (67/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-3438474077039/5000000000000),(-2223308661103/100000000000000),(10493682629/100000000000000),(-24326233/50000000000000),(144499/25000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((67/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((67/40)+(1/40)*x)) := (SharedCertificates.h61 (67/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-35344720144023/50000000000000),(-469422636193/20000000000000),(9093333903/100000000000000),(-8065921/25000000000000),(74773/10000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((67/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((67/40)+(1/40)*x)) := (SharedCertificates.h67 (67/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-17015028064861/5000000000000),(-5448449030533/50000000000000),(54526026827/100000000000000),(-1384633/500000000000),(124107/5000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((67/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((67/40)+(1/40)*x)) := (SharedCertificates.h67 (67/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-44159562200309/12500000000000),(-11719585233713/100000000000000),(5733970677/12500000000000),(-5044911/3125000000000),(1888059/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((67/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((67/40)+(1/40)*x)) := (SharedCertificates.h72 (67/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(488344981398717/100000000000000),(14911336464983/100000000000000),(-19684512303/20000000000000),(75040237/12500000000000),(4508759/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((67/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((67/40)+(1/40)*x)) := (SharedCertificates.h72 (67/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(264425413990827/25000000000000),(17476646313671/50000000000000),(-143229988193/100000000000000),(236418973/50000000000000),(6053219/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((67/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((67/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((67/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(10985730218193/10000000000000),(319712764179/100000000000000),(-147708251/10000000000000),(6654923/100000000000000),(85879/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((67/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(2744963874037823/25000000000000),(14361428979159/100000000000000),(-104749773159/100000000000000),(672377177/100000000000000),(16033201/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((67/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(227689699639/25000000000000),(-595627047/50000000000000),(10246937/100000000000000),(-80541/100000000000000),(807/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((67/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(4816555447079/50000000000000),(305740273709/100000000000000),(-1612480227/100000000000000),(2185601/25000000000000),(176671/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((67/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((67/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-26501038795863/12500000000000),(-7061685155899/100000000000000),(6312892359/25000000000000),(-15629549/12500000000000),(19533123/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((67/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(59701492537313/100000000000000),(-222766763199/25000000000000),(53198033/400000000000),(-49625031/25000000000000),(150379/5000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((67/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-126572125592181/100000000000000),(-2326795233489/100000000000000),(4980385091/10000000000000),(-817989649/100000000000000),(9246169/25000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((67/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((67/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((67/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((67/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((67/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((67/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((67/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((67/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((67/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((67/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (67/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((67/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((67/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(13443394583/100000000000000),(-401295361/50000000000000),(14973707/50000000000000),(-893953/100000000000000),(27197/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((67/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(8251517155339/6250000000000),(-781124234801/100000000000000),(4396056941/50000000000000),(-94024813/100000000000000),(523672647/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((67/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((67/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (67/40) (1/40))

def c134 : Certificate := ⟨(27489/1600),(167/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((67/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((67/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(1246105919003/20000000000000),(-7278656069/12500000000000),(68024823/12500000000000),(-5085969/100000000000000),(2999/6250000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((67/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(53522196261677/50000000000000),(60041633911/20000000000000),(544198579/50000000000000),(-10171953/100000000000000),(389799/25000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((67/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((67/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (67/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((67/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (67/40) (1/40))

def c140 : Certificate := ⟨(4913468989467/20000000000000),(-18119197299/100000000000000),(-5232721/10000000000000),(350487/50000000000000),(95081/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((67/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(54081881583/3125000000000),(36238394597/50000000000000),(209308839/100000000000000),(-2803899/100000000000000),(196857/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((67/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((67/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(5990092627/20000000000000),(2508595923/100000000000000),(59773531/100000000000000),(4127/2000000000000),(17841/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((67/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((67/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((67/40)+(1/40)*x)) := (SharedCertificates.h144 (67/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(358368900083/100000000000000),(29972908271/100000000000000),(177862947/25000000000000),(2373591/100000000000000),(214171/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((67/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((67/40)+(1/40)*x)) := (SharedCertificates.h148 (67/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-242280627487227/100000000000000),(-63412325223/625000000000),(-29268451433/100000000000000),(196577631/50000000000000),(55124919/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((67/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((67/40)+(1/40)*x)) := (SharedCertificates.h151 (67/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-488766616489479/100000000000000),(-20644686436579/100000000000000),(-66973590189/100000000000000),(378119899/50000000000000),(112737773/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((67/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((67/40)+(1/40)*x)) := (SharedCertificates.h154 (67/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(657830087254653/100000000000000),(6798010093377/25000000000000),(3964950433/6250000000000),(-8941097/781250000000),(38190091/25000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((67/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((67/40)+(1/40)*x)) := (SharedCertificates.h157 (67/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(365707152326121/20000000000000),(77047993725687/100000000000000),(241956986983/100000000000000),(-2879451061/100000000000000),(26269691/6250000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((67/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((67/40)+(1/40)*x)) := (SharedCertificates.h160 (67/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(1880441240088503/100000000000000),(81417972974931/100000000000000),(347487391913/100000000000000),(-2473037433/100000000000000),(225536683/50000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((67/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(103491190884447/100000000000000),(147462174311/100000000000000),(478391209/100000000000000),(-675181/12500000000000),(805269/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((67/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((67/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((67/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((67/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((67/40)+(1/40)*x)) := (SharedCertificates.h167 (67/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(27161555722838961/50000000000000),(14958190229/19531250000),(230458987119/100000000000000),(-1467032789/50000000000000),(214332577/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((67/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(184083711957/100000000000000),(-259525323/100000000000000),(-103767/25000000000000),(2907/25000000000000),(93/6250000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((67/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(138463441437/4000000000000),(2899940113/2000000000000),(210281161/50000000000000),(-139339/2500000000000),(875219/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((67/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((67/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((67/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (67/40) (1/40))

def c175 : Certificate := ⟨(593636439291/2500000000000),(-10156284139/20000000000000),(-75506931/100000000000000),(2275829/100000000000000),(272883/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((67/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(418180809453/25000000000000),(2708342437/4000000000000),(100675907/100000000000000),(-75861/2500000000000),(402287/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((67/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((67/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(27980030303/100000000000000),(453030733/20000000000000),(984251/2000000000000),(17/48828125000),(901/5000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((67/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((67/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((67/40)+(1/40)*x)) := (SharedCertificates.h144 (67/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(167412153349/50000000000000),(6767043681/25000000000000),(146445119/25000000000000),(173561/50000000000000),(215919/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((67/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((67/40)+(1/40)*x)) := (SharedCertificates.h148 (67/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-234175652609697/100000000000000),(-2369629762283/25000000000000),(-2813232787/20000000000000),(425241121/100000000000000),(2252909/4000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((67/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((67/40)+(1/40)*x)) := (SharedCertificates.h151 (67/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-472279617145861/100000000000000),(-3855100682831/20000000000000),(-35078069261/100000000000000),(211198911/25000000000000),(115163179/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((67/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((67/40)+(1/40)*x)) := (SharedCertificates.h154 (67/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(636098515654171/100000000000000),(25425596398999/100000000000000),(12323413709/50000000000000),(-118295391/10000000000000),(124949/80000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((67/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((67/40)+(1/40)*x)) := (SharedCertificates.h157 (67/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(441749891847331/25000000000000),(71949981981583/100000000000000),(61988839469/50000000000000),(-3182966111/100000000000000),(85866161/20000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((67/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((67/40)+(1/40)*x)) := (SharedCertificates.h160 (67/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1815473424454117/100000000000000),(3035754282597/4000000000000),(210847789693/100000000000000),(-3087123913/100000000000000),(230292367/50000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((67/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(103373426505927/100000000000000),(27536455103/20000000000000),(62641091/25000000000000),(-377129/6250000000000),(411297/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((67/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((67/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((67/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((67/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((67/40)+(1/40)*x)) := (SharedCertificates.h167 (67/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(13565484470513067/25000000000000),(71533466137387/100000000000000),(4580676463/4000000000000),(-1600910029/50000000000000),(437682761/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((67/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(18429124337/10000000000000),(-60737747/25000000000000),(-13731/20000000000000),(11477/100000000000000),(761/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((67/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(1672879273489/50000000000000),(33863755551/25000000000000),(50735681/25000000000000),(-6045299/100000000000000),(894821/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((67/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((67/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(89873472973/1000000000000),(31709093677/10000000000000),(-96123907/12500000000000),(-390599/20000000000000),(4948849/12500000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((67/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(5365580475999/100000000000000),(21844946253/20000000000000),(-261164891/12500000000000),(300179/1000000000000),(499797/2000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((67/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((67/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((67/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((67/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((67/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((67/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (67/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((67/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((67/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((67/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (67/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((67/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(9987268729/25000000000000),(-199830209/100000000000000),(1442383/50000000000000),(-1193/5000000000000),(13/5000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((67/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(470868510357571/100000000000000),(-1294195168781/100000000000000),(-629069801/25000000000000),(-24243581/50000000000000),(1195561/20000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((67/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((67/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((67/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((67/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (67/40) (1/40))

def c223 : Certificate := ⟨(21609/1600),(147/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((67/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1865483361/2560000),(10958703/640000),(179507/1280000),(287/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((67/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((67/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(155277996137/100000000000000),(-725598113/25000000000000),(317873/781250000000),(-507013/100000000000000),(1217/20000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((67/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(22630352978359/20000000000000),(543834743009/100000000000000),(69116507/4000000000000),(-2541513/25000000000000),(4465589/50000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((67/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((67/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (67/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((67/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (67/40) (1/40))

def c231 : Certificate := ⟨(4840836152603/20000000000000),(-15930071639/50000000000000),(-29645351/50000000000000),(403431/50000000000000),(526217/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((67/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(99477404623/3125000000000),(127440573111/100000000000000),(47432561/20000000000000),(-806863/25000000000000),(280409/12500000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((67/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((67/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(12666565159/12500000000000),(2028393193/25000000000000),(88755047/50000000000000),(79801/20000000000000),(15623/10000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((67/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((67/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((67/40)+(1/40)*x)) := (SharedCertificates.h144 (67/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(1209538865683/100000000000000),(24147010197/25000000000000),(1048829619/50000000000000),(4278273/100000000000000),(1871479/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((67/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((67/40)+(1/40)*x)) := (SharedCertificates.h148 (67/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-445620269739153/100000000000000),(-17837064127441/100000000000000),(-8252514367/25000000000000),(454842771/100000000000000),(157051247/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((67/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((67/40)+(1/40)*x)) := (SharedCertificates.h151 (67/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-905502872744017/100000000000000),(-9204766161823/25000000000000),(-5702805577/6250000000000),(848176557/100000000000000),(324996269/50000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((67/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((67/40)+(1/40)*x)) := (SharedCertificates.h154 (67/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1196736960744401/100000000000000),(4673858979981/10000000000000),(19666579693/50000000000000),(-1389948677/100000000000000),(173550733/20000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((67/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((67/40)+(1/40)*x)) := (SharedCertificates.h157 (67/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(1690268123565803/50000000000000),(136825548962841/100000000000000),(62535034059/20000000000000),(-3310721673/100000000000000),(37738331/1562500000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((67/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((67/40)+(1/40)*x)) := (SharedCertificates.h160 (67/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1778832228737961/50000000000000),(151140023619731/100000000000000),(316852427591/50000000000000),(-592966293/25000000000000),(268901727/10000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((67/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(13308485802143/12500000000000),(131497359497/50000000000000),(81479463/12500000000000),(-6055899/100000000000000),(2321387/50000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((67/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((67/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((67/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((67/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((67/40)+(1/40)*x)) := (SharedCertificates.h167 (67/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(55861656092000377/100000000000000),(135267200155657/100000000000000),(275751883661/100000000000000),(-3474944529/100000000000000),(1244581843/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((67/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(179013668759/100000000000000),(-433475831/100000000000000),(20747/12500000000000),(12873/100000000000000),(8077/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((67/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(3184352833731/50000000000000),(255139685673/100000000000000),(242583853/50000000000000),(-3142043/50000000000000),(5155851/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((67/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((67/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((67/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (67/40) (1/40))

def c259 : Certificate := ⟨(22755443206997/100000000000000),(-84480952387/100000000000000),(45221379/100000000000000),(2407861/100000000000000),(1413177/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((67/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(299274239067/10000000000000),(112641269849/100000000000000),(-30147587/50000000000000),(-1605241/50000000000000),(45119/2000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((67/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((67/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(89565070169/100000000000000),(421382879/6250000000000),(61635799/50000000000000),(-163999/50000000000000),(147317/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((67/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((67/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((67/40)+(1/40)*x)) := (SharedCertificates.h144 (67/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(1069419938383/100000000000000),(80300189373/100000000000000),(1456799947/100000000000000),(-1045043/25000000000000),(353/20000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((67/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((67/40)+(1/40)*x)) := (SharedCertificates.h148 (67/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-41895192970997/10000000000000),(-3153233998571/20000000000000),(8574728973/100000000000000),(90180117/20000000000000),(157936871/50000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((67/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((67/40)+(1/40)*x)) := (SharedCertificates.h151 (67/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-850506021384561/100000000000000),(-8120827296041/25000000000000),(-367338023/100000000000000),(118130569/12500000000000),(65229199/10000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((67/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((67/40)+(1/40)*x)) := (SharedCertificates.h154 (67/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1126752366170773/100000000000000),(10359181586347/25000000000000),(-2965071667/5000000000000),(-232255077/20000000000000),(872451387/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((67/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((67/40)+(1/40)*x)) := (SharedCertificates.h157 (67/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(3176100305903769/100000000000000),(60391307994701/50000000000000),(-3817838879/20000000000000),(-3533716497/100000000000000),(484960289/20000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((67/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((67/40)+(1/40)*x)) := (SharedCertificates.h160 (67/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(3332484510653463/100000000000000),(26531591574499/20000000000000),(203819560877/100000000000000),(-198755461/5000000000000),(1341900749/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((67/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(106075049851509/100000000000000),(116012332881/50000000000000),(429/16000000000),(-3374481/50000000000000),(4659217/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((67/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((67/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((67/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((67/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((67/40)+(1/40)*x)) := (SharedCertificates.h167 (67/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(55659474221300363/100000000000000),(29873674658509/25000000000000),(-11177574657/25000000000000),(-1760929149/50000000000000),(1247295743/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((67/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(179663932149/100000000000000),(-192859237/50000000000000),(194483/20000000000000),(897/10000000000000),(8133/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((67/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(374204544381/6250000000000),(225484495021/100000000000000),(-56545217/50000000000000),(-3169549/50000000000000),(1285819/25000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((67/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((67/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(5818041132651/10000000000000),(1051598722417/50000000000000),(-4779131133/100000000000000),(-16467783/20000000000000),(12368863/25000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((67/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(17367286963137/50000000000000),(36860689453/5000000000000),(-13856403499/100000000000000),(15765443/10000000000000),(8969183/25000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((67/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((67/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((67/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((67/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((67/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((67/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (67/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((67/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(484740053966009751/50000000000000),(969891854474013/20000000000000),(-45749615777077/100000000000000),0,(62897/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((67/40)+(1/40)*x)) := (SharedCertificates.h297 (67/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(10314806789/100000000000000),(-25797969/50000000000000),(744843/100000000000000),(-6161/100000000000000),(69/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((67/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(154472693030219/25000000000000),(196739172967/25000000000000),(1498623521/20000000000000),(-369183/100000000000000),(3883163/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((67/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((67/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (67/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((67/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (67/40) (1/40))

def c307 : Certificate := ⟨(2598926375868877/100000000000000),(11091229182759/50000000000000),0,0,(1037/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((67/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (67/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((67/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (67/40) (1/40))

def c311 : Certificate := ⟨(129754601508179/6250000000000),(2817541634481/100000000000000),0,0,(1037/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((67/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (67/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2408392429769/50000000000000),(-408568479/6250000000000),(4435907/50000000000000),(-12041/100000000000000),(1/5000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((67/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(125184692183391/100000000000000),(224646748149/25000000000000),(-121951661/10000000000000),(1655049/100000000000000),(3247/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((67/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((67/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (67/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((67/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (67/40) (1/40))

def c316 : Certificate := ⟨(2939898879193/12500000000000),(-49705550383/100000000000000),(21563219/12500000000000),(-59869/10000000000000),(2143/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((67/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(5923235865821/100000000000000),(198822201529/100000000000000),(-690023009/100000000000000),(2394757/100000000000000),(9643/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((67/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((67/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(350847231221/100000000000000),(235534159/1000000000000),(313559297/100000000000000),(-153759/6250000000000),(31/200000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((67/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((67/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((67/40)+(1/40)*x)) := (SharedCertificates.h144 (67/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(521075469573/12500000000000),(55691123533/20000000000000),(3636748863/100000000000000),(-6033779/20000000000000),(197331/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((67/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((67/40)+(1/40)*x)) := (SharedCertificates.h148 (67/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-829006104982127/100000000000000),(-27810326521283/100000000000000),(97343501737/100000000000000),(-331643871/100000000000000),(288087/20000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((67/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((67/40)+(1/40)*x)) := (SharedCertificates.h151 (67/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-426902507342507/25000000000000),(-29482867925883/50000000000000),(37349889289/25000000000000),(-162295273/50000000000000),(60907/1250000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((67/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((67/40)+(1/40)*x)) := (SharedCertificates.h154 (67/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1089650019316541/50000000000000),(2176836253757/3125000000000),(-181131821187/50000000000000),(97861169/6250000000000),(868261/12500000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((67/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((67/40)+(1/40)*x)) := (SharedCertificates.h157 (67/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(1269696548124843/20000000000000),(217222296583309/100000000000000),(-622522480717/100000000000000),(729253267/50000000000000),(28231/156250000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((67/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((67/40)+(1/40)*x)) := (SharedCertificates.h160 (67/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(1742867218092067/25000000000000),(25974087586221/10000000000000),(-1105539393/5000000000000),(-2481855573/100000000000000),(7689741/20000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((67/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(112197318962863/100000000000000),(210598909479/50000000000000),(-1066486721/100000000000000),(232937/10000000000000),(17393/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((67/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((67/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((67/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((67/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((67/40)+(1/40)*x)) := (SharedCertificates.h167 (67/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(29389797740785587/50000000000000),(106169537703639/50000000000000),(-28031821371/4000000000000),(1752916897/100000000000000),(27880669/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((67/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(170127063959/100000000000000),(-614577613/100000000000000),(2124233/50000000000000),(-27749/100000000000000),(127/50000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((67/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(94882842459/800000000000),(199522219509/50000000000000),(-53509809/4000000000000),(5014069/100000000000000),(141883/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((67/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((67/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((67/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (67/40) (1/40))

def c344 : Certificate := ⟨(21028102781797/100000000000000),(-11920145723/10000000000000),(837488349/100000000000000),(-5884043/100000000000000),(4177/10000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((67/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(2647931478801/50000000000000),(31787055261/20000000000000),(-558325567/50000000000000),(784539/10000000000000),(7673/10000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((67/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((67/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(280461644657/100000000000000),(1052124303/6250000000000),(16791449/12500000000000),(-2718543/100000000000000),(22979/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((67/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((67/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((67/40)+(1/40)*x)) := (SharedCertificates.h144 (67/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(208489625449/6250000000000),(49833337809/25000000000000),(387626083/25000000000000),(-32429629/100000000000000),(556317/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((67/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((67/40)+(1/40)*x)) := (SharedCertificates.h148 (67/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-741244152866767/100000000000000),(-11117540222297/50000000000000),(19586604091/12500000000000),(-27489297/2500000000000),(5411927/50000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((67/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((67/40)+(1/40)*x)) := (SharedCertificates.h151 (67/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-761048451322811/50000000000000),(-5857189399589/12500000000000),(293898279903/100000000000000),(-36315321/2000000000000),(27927287/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((67/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((67/40)+(1/40)*x)) := (SharedCertificates.h154 (67/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1958299072630753/100000000000000),(56289422669419/100000000000000),(-7372231959/1562500000000),(237202703/6250000000000),(39820361/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((67/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((67/40)+(1/40)*x)) := (SharedCertificates.h157 (67/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(1132872988133723/20000000000000),(172975478846411/100000000000000),(-564937200673/50000000000000),(7213837161/100000000000000),(25020411/25000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((67/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((67/40)+(1/40)*x)) := (SharedCertificates.h160 (67/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(6160610114834627/100000000000000),(203208476878923/100000000000000),(-217205292669/25000000000000),(487181821/20000000000000),(176091887/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((67/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((67/40)+(1/40)*x)) := (SharedCertificates.h41 (67/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(110872187559861/100000000000000),(167352270729/50000000000000),(-524742669/25000000000000),(12972237/100000000000000),(99709/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((67/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((67/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((67/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((67/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((67/40)+(1/40)*x)) := (SharedCertificates.h167 (67/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(58109947971307287/100000000000000),(169544961456861/100000000000000),(-291192154481/25000000000000),(192952049/2500000000000),(123718483/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((67/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(172087574487/100000000000000),(-502092709/100000000000000),(614287/12500000000000),(-47259/100000000000000),(169/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((67/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(10601644520219/100000000000000),(79691141199/25000000000000),(-221267761/10000000000000),(15629007/100000000000000),(249223/50000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((67/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((67/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(13879062416851/10000000000000),(461204180679/10000000000000),(-2921157003/20000000000000),(76657359/50000000000000),(1173983/20000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((67/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(82860074130453/100000000000000),(758370135381/50000000000000),(-31357786141/100000000000000),(69944729/12500000000000),(20384151/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((67/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((67/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(2105634713867187/100000000000000),(36347091064453/25000000000000),(408499/10240000),(5561/10240000),(367187501/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((67/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(34969/1600),(187/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((67/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(6539203/64000),(104907/64000),(561/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((67/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(53785831397751761/25000000000000),(18306560135116281/100000000000000),(332187664058929/50000000000000),(1339516717517/10000000000000),(164919583647/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((67/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(9296128497/20000000000000),(-791008203/20000000000000),(192999731/100000000000000),(-7102919/100000000000000),(166611/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((67/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2673894842433/50000000000000),(25470013443/50000000000000),(-1217495701/50000000000000),(1423743/2500000000000),(15429397/20000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((67/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((67/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((67/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel13

namespace Hf4Quad.Panel14
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(69/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((69/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (69/40) (1/40)

def c3 : Certificate := ⟨(151142857142857/50000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((69/40)+(1/40)*x)) := (SharedCertificates.h2 (69/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((69/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-210857142857143/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((69/40)+(1/40)*x)) := (SharedCertificates.h4 (69/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(4761/1600),(69/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((69/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(360223809523809/100000000000000),(10441269841269/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((69/40)+(1/40)*x)) := (SharedCertificates.h8 (69/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((69/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((69/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(328509/64000),(14283/64000),(207/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((69/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(64010587/1280000),(2783069/1280000),(1575559895833/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((69/40)+(1/40)*x)) := (SharedCertificates.h13 (69/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((69/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((69/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(22667121/2560000),(328509/640000),(14283/1280000),(69/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((69/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(618398638392857/25000000000000),(28679357142857/20000000000000),(3117321428571/100000000000000),(30119047619/100000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((69/40)+(1/40)*x)) := (SharedCertificates.h18 (69/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((69/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(381843591064453/25000000000000),(27669825439453/25000000000000),(328509/10240000),(4761/10240000),(168945313/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((69/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(621910071002197/6250000000000),(5633243396759/781250000000),(10450074707031/50000000000000),(60580143229/20000000000000),(110064743/5000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((69/40)+(1/40)*x)) := (SharedCertificates.h22 (69/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((69/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(105388831133789/4000000000000),(229106154638671/100000000000000),(1660189526367/20000000000000),(40101196289/25000000000000),(1753662113/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((69/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(5916272477933869/100000000000000),(514458476342073/100000000000000),(2329974983433/12500000000000),(360189369419/100000000000000),(984463229/25000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((69/40)+(1/40)*x)) := (SharedCertificates.h26 (69/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((69/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(90897866852893/2000000000000),(18443045448413/4000000000000),(10023394265441/50000000000000),(484221945189/100000000000000),(7079028329/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((69/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(134813800540749/12500000000000),(13676762373699/12500000000000),(4757134738677/100000000000000),(114906636199/100000000000000),(839932331/50000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((69/40)+(1/40)*x)) := (SharedCertificates.h30 (69/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((69/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((69/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((69/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((69/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((69/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (69/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((69/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((69/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (69/40) (1/40))

def c43 : Certificate := ⟨(11881/1600),(109/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((69/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((69/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(32063999743/50000000000000),(-588330271/50000000000000),(253009/1562500000000),(-7923/4000000000000),(467/20000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((69/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-208849062726029/20000000000000),(213446237977/100000000000000),(-998000249/50000000000000),(291713/1562500000000),(15159097/20000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((69/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((69/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (69/40) (1/40))

def c52 : Certificate := ⟨(24833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((69/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (69/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((69/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (69/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((69/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (69/40) (1/40))

def c56 : Certificate := ⟨(5893909626719/25000000000000),(-23158780459/50000000000000),(22749293/25000000000000),(-178777/100000000000000),(71/20000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((69/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(2848722986247/50000000000000),(46317560917/25000000000000),(-90997173/25000000000000),(143021/20000000000000),(1583/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((69/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((69/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((69/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((69/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((69/40)+(1/40)*x)) := (SharedCertificates.h61 (69/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-40855948525743/50000000000000),(-1360225737893/50000000000000),(657038921/20000000000000),(-240803/10000000000000),(47161/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((69/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((69/40)+(1/40)*x)) := (SharedCertificates.h61 (69/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-3376789392101/4000000000000),(-1450083747583/50000000000000),(270124431/50000000000000),(5255631/100000000000000),(31091/50000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((69/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((69/40)+(1/40)*x)) := (SharedCertificates.h67 (69/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-403630986855077/100000000000000),(-6645278590641/50000000000000),(2044411973/10000000000000),(-38804401/100000000000000),(32209/25000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((69/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((69/40)+(1/40)*x)) := (SharedCertificates.h67 (69/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-421817875478893/100000000000000),(-14473947484473/100000000000000),(3489724591/100000000000000),(38873/125000000000),(91657/25000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((69/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((69/40)+(1/40)*x)) := (SharedCertificates.h72 (69/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(287099490777069/50000000000000),(1784722724139/10000000000000),(-63300535893/100000000000000),(8311897/6250000000000),(15001/6250000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((69/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((69/40)+(1/40)*x)) := (SharedCertificates.h72 (69/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(252378601544211/20000000000000),(43068063134141/100000000000000),(-4339897783/20000000000000),(-38187897/20000000000000),(318029/20000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((69/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((69/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((69/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(55859750425541/50000000000000),(24478239463/6250000000000),(-426202871/100000000000000),(162969/100000000000000),(1467/20000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((69/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(69138787363637/625000000000),(8523621144243/50000000000000),(-4730828453/6250000000000),(32969321/20000000000000),(350781/25000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((69/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(903978828429/100000000000000),(-1393062663/100000000000000),(8332241/100000000000000),(-8961/25000000000000),(63/25000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((69/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(1425905703403/12500000000000),(371747212209/100000000000000),(-690979927/100000000000000),(214057/12500000000000),(16141/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((69/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((69/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((69/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (69/40) (1/40))

def c87 : Certificate := ⟨(21164021164021/100000000000000),(-55989473979/50000000000000),(296240603/50000000000000),(-1567411/50000000000000),(16677/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((69/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(5114638447971/100000000000000),(149305263943/100000000000000),(-394987471/50000000000000),(4179761/100000000000000),(3787/12500000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((69/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((69/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((69/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((69/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((69/40)+(1/40)*x)) := (SharedCertificates.h61 (69/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-36587254929401/50000000000000),(-34092356069/1562500000000),(5103488911/50000000000000),(-146651/312500000000),(278007/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((69/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((69/40)+(1/40)*x)) := (SharedCertificates.h61 (69/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-75347549886947/100000000000000),(-2311123938371/100000000000000),(890205183/10000000000000),(-7874821/25000000000000),(718949/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((69/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((69/40)+(1/40)*x)) := (SharedCertificates.h67 (69/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-90469611528523/25000000000000),(-333814748993/3125000000000),(13224537693/25000000000000),(-265795161/100000000000000),(59917/2500000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((69/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((69/40)+(1/40)*x)) := (SharedCertificates.h67 (69/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-188266732748921/50000000000000),(-5769010702519/50000000000000),(11228412099/25000000000000),(-157937971/100000000000000),(906331/25000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((69/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((69/40)+(1/40)*x)) := (SharedCertificates.h72 (69/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(129444677910281/25000000000000),(7262370175301/50000000000000),(-23725637867/25000000000000),(573264669/100000000000000),(433739/10000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((69/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((69/40)+(1/40)*x)) := (SharedCertificates.h72 (69/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1127039092195921/100000000000000),(17193011540511/50000000000000),(-14041082291/10000000000000),(466801837/100000000000000),(11583937/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((69/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((69/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((69/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(27622718040119/25000000000000),(156941688377/50000000000000),(-143783799/10000000000000),(1607033/25000000000000),(82573/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((69/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11008164670803069/100000000000000),(6975186150063/50000000000000),(-100809657503/100000000000000),(320642161/50000000000000),(1919273/12500000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((69/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(908416643377/100000000000000),(-1151213737/100000000000000),(9777927/100000000000000),(-37927/50000000000000),(1527/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((69/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(1279776336359/12500000000000),(74848431953/25000000000000),(-1561170847/100000000000000),(836427/10000000000000),(42111/25000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((69/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((69/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-113015831607789/50000000000000),(-6962156401819/100000000000000),(4903692117/20000000000000),(-2984693/2500000000000),(19205579/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((69/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(57971014492753/100000000000000),(-84015963033/10000000000000),(6088113263/50000000000000),(-44116763/25000000000000),(2595107/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((69/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-65516424120457/50000000000000),(-1068502955303/50000000000000),(22592350247/50000000000000),(-724061003/100000000000000),(33676877/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((69/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((69/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((69/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((69/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((69/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((69/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((69/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((69/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((69/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((69/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (69/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((69/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((69/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(5975603847/50000000000000),(-138564727/20000000000000),(5020461/20000000000000),(-181901/25000000000000),(21433/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((69/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(32624114705443/25000000000000),(-373525646443/50000000000000),(4126115273/50000000000000),(-86137049/100000000000000),(458981379/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((69/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((69/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (69/40) (1/40))

def c134 : Certificate := ⟨(28161/1600),(169/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((69/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((69/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(611620795107/10000000000000),(-876749993/1562500000000),(257394493/50000000000000),(-944567/20000000000000),(43733/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((69/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(107649082568801/100000000000000),(76110666887/25000000000000),(25739449/2500000000000),(-377827/4000000000000),(291581/20000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((69/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((69/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (69/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((69/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (69/40) (1/40))

def c140 : Certificate := ⟨(12265451374237/50000000000000),(-9160149979/50000000000000),(-24137177/50000000000000),(65073/10000000000000),(44329/50000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((69/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1876389006103/100000000000000),(7328119983/10000000000000),(48274353/25000000000000),(-650731/25000000000000),(73637/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((69/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((69/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(17604178511/50000000000000),(1375040377/50000000000000),(60947859/100000000000000),(92663/50000000000000),(4453/25000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((69/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((69/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((69/40)+(1/40)*x)) := (SharedCertificates.h144 (69/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(421178992783/100000000000000),(32846162409/100000000000000),(11326883/1562500000000),(1059421/50000000000000),(213751/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((69/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((69/40)+(1/40)*x)) := (SharedCertificates.h148 (69/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-32835819737263/12500000000000),(-10258443009401/100000000000000),(-6748788001/25000000000000),(36503281/10000000000000),(12887689/25000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((69/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((69/40)+(1/40)*x)) := (SharedCertificates.h151 (69/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-530317943401751/100000000000000),(-10451862055323/50000000000000),(-62598560491/100000000000000),(702914527/100000000000000),(105585827/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((69/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((69/40)+(1/40)*x)) := (SharedCertificates.h154 (69/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(712458939762273/100000000000000),(27432403401633/100000000000000),(56825381051/100000000000000),(-1061370083/100000000000000),(35718999/25000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((69/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((69/40)+(1/40)*x)) := (SharedCertificates.h157 (69/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(1983576957626847/100000000000000),(77982096882391/100000000000000),(225297081931/100000000000000),(-535383363/20000000000000),(49186273/12500000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((69/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((69/40)+(1/40)*x)) := (SharedCertificates.h160 (69/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(408929539265831/20000000000000),(1034736659937/1250000000000),(333160085989/100000000000000),(-576356829/25000000000000),(424256801/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((69/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(25946996592307/25000000000000),(74656240207/50000000000000),(447142683/100000000000000),(-2510261/50000000000000),(377091/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((69/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((69/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((69/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((69/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((69/40)+(1/40)*x)) := (SharedCertificates.h167 (69/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(1089543641994737/2000000000000),(19368350671481/25000000000000),(213481045269/100000000000000),(-682086407/25000000000000),(40183053/10000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((69/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(183563092189/100000000000000),(-130524899/50000000000000),(-43511/12500000000000),(10711/100000000000000),(1387/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((69/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(469152316969/12500000000000),(73307010019/50000000000000),(77669509/20000000000000),(-5170769/100000000000000),(205793/25000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((69/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((69/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((69/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (69/40) (1/40))

def c175 : Certificate := ⟨(738862829099/3125000000000),(-10211378227/20000000000000),(-975193/1562500000000),(418347/20000000000000),(6327/2500000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((69/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(904259645887/50000000000000),(13615170969/20000000000000),(83216469/100000000000000),(-2788981/100000000000000),(376157/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((69/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((69/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(32707420287/100000000000000),(492465987/20000000000000),(49353191/100000000000000),(6211/50000000000000),(8927/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((69/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((69/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((69/40)+(1/40)*x)) := (SharedCertificates.h144 (69/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(48913250429/12500000000000),(7353591021/25000000000000),(587046227/100000000000000),(15829/20000000000000),(42787/20000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((69/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((69/40)+(1/40)*x)) := (SharedCertificates.h148 (69/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-253185624003799/100000000000000),(-1905964265789/20000000000000),(-2323867821/20000000000000),(97717993/25000000000000),(52664933/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((69/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((69/40)+(1/40)*x)) := (SharedCertificates.h151 (69/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-127741078137707/25000000000000),(-19405946291691/100000000000000),(-30208948781/100000000000000),(194801157/25000000000000),(107823449/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((69/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((69/40)+(1/40)*x)) := (SharedCertificates.h154 (69/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(687039039166427/100000000000000),(12755200254583/50000000000000),(1785603561/10000000000000),(-216425773/20000000000000),(9127693/6250000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((69/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((69/40)+(1/40)*x)) := (SharedCertificates.h157 (69/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(1911370489928043/100000000000000),(36204357900449/50000000000000),(26409593787/25000000000000),(-586755489/20000000000000),(401820711/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((69/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((69/40)+(1/40)*x)) := (SharedCertificates.h160 (69/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1968080264457947/100000000000000),(76701062376167/100000000000000),(48241281957/25000000000000),(-115072841/4000000000000),(108210037/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((69/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(20729949200767/20000000000000),(1108912317/800000000000),(215786129/100000000000000),(-278277/5000000000000),(96271/12500000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((69/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((69/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((69/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((69/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((69/40)+(1/40)*x)) := (SharedCertificates.h167 (69/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(6800679723403379/12500000000000),(71954147026149/100000000000000),(24019173529/25000000000000),(-2948613837/100000000000000),(410107083/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((69/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(45951289093/25000000000000),(-48618461/20000000000000),(-1543/50000000000000),(2079/20000000000000),(709/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((69/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(3617433007613/100000000000000),(3404906399/2500000000000),(168164739/100000000000000),(-2777307/50000000000000),(168123/20000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((69/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((69/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(9618439256183/100000000000000),(9812338991/3125000000000),(-389132921/50000000000000),(-1164383/100000000000000),(18716629/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((69/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(2787953407589/50000000000000),(4048630199/4000000000000),(-479515901/25000000000000),(13561509/50000000000000),(4583531/20000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((69/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((69/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((69/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((69/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((69/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((69/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (69/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((69/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((69/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((69/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (69/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((69/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(39560766697/100000000000000),(-47142369/25000000000000),(2747551/100000000000000),(-21909/100000000000000),(119/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((69/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(93653933785351/20000000000000),(-652419191393/50000000000000),(-1402228819/50000000000000),(-23807521/50000000000000),(2750019/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((69/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((69/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((69/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((69/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (69/40) (1/40))

def c223 : Certificate := ⟨(22201/1600),(149/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((69/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1954598241/2560000),(11321169/640000),(182963/1280000),(289/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((69/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((69/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(74815999401/50000000000000),(-2745541263/100000000000000),(37782677/100000000000000),(-231087/50000000000000),(5443/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((69/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(114246266271759/100000000000000),(34414220257/6250000000000),(1669236819/100000000000000),(-9405681/100000000000000),(4188153/50000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((69/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((69/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (69/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((69/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (69/40) (1/40))

def c231 : Certificate := ⟨(12070114825657/50000000000000),(-3208785683/10000000000000),(-5462283/10000000000000),(750023/100000000000000),(490947/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((69/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(171954069737/5000000000000),(128351427319/100000000000000),(54622829/25000000000000),(-1500047/50000000000000),(2103661/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((69/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((69/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(29568202099/25000000000000),(8828220113/100000000000000),(179769077/100000000000000),(177261/50000000000000),(78671/50000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((69/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((69/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((69/40)+(1/40)*x)) := (SharedCertificates.h144 (69/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(705569352227/50000000000000),(105027812329/100000000000000),(2121684989/100000000000000),(149477/4000000000000),(94211/5000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((69/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((69/40)+(1/40)*x)) := (SharedCertificates.h148 (69/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-240711432527481/50000000000000),(-17963776616039/100000000000000),(-6075585971/20000000000000),(42305203/10000000000000),(29455867/10000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((69/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((69/40)+(1/40)*x)) := (SharedCertificates.h151 (69/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-97949931470933/10000000000000),(-37174101667453/100000000000000),(-17266184211/20000000000000),(790778763/100000000000000),(611057373/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((69/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((69/40)+(1/40)*x)) := (SharedCertificates.h154 (69/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(10322884466249/800000000000),(23439825276349/50000000000000),(31296554989/100000000000000),(-645241959/50000000000000),(81383437/10000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((69/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((69/40)+(1/40)*x)) := (SharedCertificates.h157 (69/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(3655412014361909/100000000000000),(69018712109571/50000000000000),(293482222171/100000000000000),(-1545296991/50000000000000),(2269008757/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((69/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((69/40)+(1/40)*x)) := (SharedCertificates.h160 (69/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1931230326725511/50000000000000),(30729396884559/20000000000000),(619921590869/100000000000000),(-2225429567/100000000000000),(2545325017/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((69/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(26749108899469/25000000000000),(265531074751/100000000000000),(616751709/100000000000000),(-2822833/50000000000000),(545583/12500000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((69/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((69/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((69/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((69/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((69/40)+(1/40)*x)) := (SharedCertificates.h167 (69/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(56133266166766353/100000000000000),(34082358923399/25000000000000),(255591596291/100000000000000),(-3248873117/100000000000000),(2343599923/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((69/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(178147481571/100000000000000),(-216331129/50000000000000),(59909/25000000000000),(5849/50000000000000),(7533/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((69/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(6880876380793/100000000000000),(257006823781/100000000000000),(89771607/20000000000000),(-582669/10000000000000),(487719/10000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((69/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((69/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((69/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (69/40) (1/40))

def c259 : Certificate := ⟨(22586680965749/100000000000000),(-84272136877/100000000000000),(29475749/50000000000000),(434549/20000000000000),(261163/20000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((69/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(3217758712333/100000000000000),(7022678073/6250000000000),(-78601999/100000000000000),(-579399/20000000000000),(2113143/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((69/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((69/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(103539711307/100000000000000),(7231130737/100000000000000),(121195653/100000000000000),(-90769/25000000000000),(147199/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((69/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((69/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((69/40)+(1/40)*x)) := (SharedCertificates.h144 (69/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(1235813219521/100000000000000),(43037763913/50000000000000),(357615207/25000000000000),(-2294269/50000000000000),(881683/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((69/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((69/40)+(1/40)*x)) := (SharedCertificates.h148 (69/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-450446454239081/100000000000000),(-15726640585781/100000000000000),(11146054179/100000000000000),(406935499/100000000000000),(295883293/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((69/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((69/40)+(1/40)*x)) := (SharedCertificates.h151 (69/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-457733359739457/50000000000000),(-16236888792303/50000000000000),(2525185663/50000000000000),(862187691/100000000000000),(12245789/2000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((69/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((69/40)+(1/40)*x)) := (SharedCertificates.h154 (69/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1209379594123663/100000000000000),(10296531158259/25000000000000),(-65868147437/100000000000000),(-1029879151/100000000000000),(163439639/20000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((69/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((69/40)+(1/40)*x)) := (SharedCertificates.h157 (69/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(3417561565204741/100000000000000),(24133031021853/20000000000000),(-983106761/2500000000000),(-3216403887/100000000000000),(14217147/625000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((69/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((69/40)+(1/40)*x)) := (SharedCertificates.h160 (69/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(3598584417977089/100000000000000),(66713278901213/50000000000000),(90365124913/50000000000000),(-931228087/25000000000000),(1267004949/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((69/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(106539057135973/100000000000000),(231956829073/100000000000000),(-7201669/20000000000000),(-3078533/50000000000000),(874697/20000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((69/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((69/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((69/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((69/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((69/40)+(1/40)*x)) := (SharedCertificates.h167 (69/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(3493641079577917/6250000000000),(2385498585853/2000000000000),(-32424593191/50000000000000),(-1598168517/50000000000000),(1172341687/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((69/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(178896453803/100000000000000),(-381726783/100000000000000),(511033/50000000000000),(1521/20000000000000),(947/12500000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((69/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(1609434977717/25000000000000),(224958619807/100000000000000),(-4663281/3125000000000),(-5716253/100000000000000),(2425973/50000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((69/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((69/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(12473408082917/20000000000000),(2083111569601/100000000000000),(-2629647197/50000000000000),(-7782001/10000000000000),(46532339/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((69/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(112983768867/312500000000),(341809106859/50000000000000),(-647818833/5000000000000),(35665131/25000000000000),(6541513/20000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((69/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((69/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((69/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((69/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((69/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((69/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (69/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((69/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(97899602801365133/10000000000000),(4666460809261761/100000000000000),(-45749615777077/100000000000000),0,(63499/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((69/40)+(1/40)*x)) := (SharedCertificates.h297 (69/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(5107273019/50000000000000),(-4868843/10000000000000),(354707/50000000000000),(-5657/100000000000000),(1/1562500000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((69/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(619494660953697/100000000000000),(102117037611/12500000000000),(1499883019/20000000000000),(37719/1562500000000),(1805509/25000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((69/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((69/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (69/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((69/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (69/40) (1/40))

def c307 : Certificate := ⟨(1321645646299957/50000000000000),(11091229182759/50000000000000),0,0,(13/1250000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((69/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (69/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((69/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (69/40) (1/40))

def c311 : Certificate := ⟨(2081708707399827/100000000000000),(2817541634481/100000000000000),0,0,(1039/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((69/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (69/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(1200936514851/25000000000000),(-6501752371/100000000000000),(4399981/50000000000000),(-11911/100000000000000),(1/5000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((69/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(126977001306837/100000000000000),(893728715323/100000000000000),(-302409971/25000000000000),(327441/20000000000000),(807/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((69/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((69/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (69/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((69/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (69/40) (1/40))

def c316 : Certificate := ⟨(292755814991/1250000000000),(-24511322871/50000000000000),(84481453/50000000000000),(-36397/6250000000000),(259/12500000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((69/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(6318139202877/100000000000000),(39218116593/20000000000000),(-5406813/800000000000),(2329407/100000000000000),(4699/50000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((69/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((69/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(399188829869/100000000000000),(2477855199/10000000000000),(149556337/50000000000000),(-2356213/100000000000000),(7481/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((69/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((69/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((69/40)+(1/40)*x)) := (SharedCertificates.h144 (69/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(4739823346521/100000000000000),(146322996829/50000000000000),(864943603/25000000000000),(-28833547/100000000000000),(11873/6250000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((69/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((69/40)+(1/40)*x)) := (SharedCertificates.h148 (69/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-884240019765777/100000000000000),(-13712448743309/50000000000000),(3815185517/4000000000000),(-103367/32000000000),(1401063/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((69/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((69/40)+(1/40)*x)) := (SharedCertificates.h151 (69/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-1824946492141909/100000000000000),(-2918600891961/5000000000000),(73731591239/50000000000000),(-160429189/50000000000000),(2364849/50000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((69/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((69/40)+(1/40)*x)) := (SharedCertificates.h154 (69/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1158590466678049/50000000000000),(34114150441837/50000000000000),(-35301404603/10000000000000),(1517708629/100000000000000),(6751497/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((69/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((69/40)+(1/40)*x)) := (SharedCertificates.h157 (69/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(1695112219993203/25000000000000),(21474964473941/10000000000000),(-613819557127/100000000000000),(1442395487/100000000000000),(2187717/12500000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((69/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((69/40)+(1/40)*x)) := (SharedCertificates.h160 (69/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(7490842560654043/100000000000000),(129811559285327/50000000000000),(-4581505213/12500000000000),(-2366031663/100000000000000),(749401/2000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((69/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(113035467235623/100000000000000),(2605998237/625000000000),(-65786911/6250000000000),(2302601/100000000000000),(16879/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((69/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((69/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((69/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((69/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((69/40)+(1/40)*x)) := (SharedCertificates.h167 (69/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(592014844366187/1000000000000),(10477842709397/5000000000000),(-345166887203/50000000000000),(1734223151/100000000000000),(6736751/25000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((69/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(329911491/195312500000),(-119582237/20000000000000),(127691/3125000000000),(-1649/6250000000000),(239/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((69/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(12653132994721/100000000000000),(15750119329/4000000000000),(-1308142129/100000000000000),(4854679/100000000000000),(68991/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((69/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((69/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((69/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (69/40) (1/40))

def c344 : Certificate := ⟨(4158600680131/20000000000000),(-57960406167/50000000000000),(80315349/10000000000000),(-5564621/100000000000000),(38959/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((69/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(44874630393/800000000000),(154561083111/100000000000000),(-535435661/50000000000000),(7419493/100000000000000),(72963/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((69/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((69/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(157322847883/50000000000000),(8669839347/50000000000000),(118753897/100000000000000),(-1238967/50000000000000),(21489/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((69/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((69/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((69/40)+(1/40)*x)) := (SharedCertificates.h144 (69/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(233778082871/6250000000000),(51289556389/25000000000000),(1364862281/100000000000000),(-29499631/100000000000000),(129809/25000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((69/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((69/40)+(1/40)*x)) := (SharedCertificates.h148 (69/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-196274054444061/25000000000000),(-21621262357119/100000000000000),(150275584069/100000000000000),(-8126513/781250000000),(5143793/50000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((69/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((69/40)+(1/40)*x)) := (SharedCertificates.h151 (69/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-403662672999891/25000000000000),(-45703364184871/100000000000000),(14163136737/5000000000000),(-865126307/50000000000000),(1322749/5000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((69/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((69/40)+(1/40)*x)) := (SharedCertificates.h154 (69/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1034510260695761/50000000000000),(5444674343033/10000000000000),(-89949020861/20000000000000),(1783444261/50000000000000),(9402411/25000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((69/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((69/40)+(1/40)*x)) := (SharedCertificates.h157 (69/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(600585340304747/10000000000000),(21067641831703/12500000000000),(-271911410201/25000000000000),(3432935761/50000000000000),(1480777/1562500000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((69/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((69/40)+(1/40)*x)) := (SharedCertificates.h160 (69/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(6563571368221991/100000000000000),(199762614215163/100000000000000),(-854066045477/100000000000000),(2480062893/100000000000000),(83193723/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((69/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((69/40)+(1/40)*x)) := (SharedCertificates.h41 (69/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(1742707863969/1562500000000),(81615461229/25000000000000),(-2022988747/100000000000000),(3090263/25000000000000),(23613/12500000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((69/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((69/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((69/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((69/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((69/40)+(1/40)*x)) := (SharedCertificates.h167 (69/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(29222219893418959/50000000000000),(164976953490929/100000000000000),(-44784687071/4000000000000),(7336247639/100000000000000),(58395993/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((69/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(5346958601/3125000000000),(-2414943/500000000000),(928237/20000000000000),(-5479/12500000000000),(311/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((69/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(11230446201789/100000000000000),(155048937787/50000000000000),(-265191627/12500000000000),(14762903/100000000000000),(467247/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((69/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((69/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(147957497967027/100000000000000),(71178626871/1562500000000),(-13705512499/100000000000000),(73436431/50000000000000),(701457/12500000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((69/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(85772462589579/100000000000000),(1397751046379/100000000000000),(-1410124309/5000000000000),(49387537/10000000000000),(4560789/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((69/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((69/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(301601097290039/12500000000000),(40502208251953/25000000000000),(442773/10240000),(1173/2048000),(188476563/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((69/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(35721/1600),(189/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((69/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(6751269/64000),(107163/64000),(567/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((69/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(127261883656264019/50000000000000),(21130141236296211/100000000000000),(748774984769713/100000000000000),(3688755407501/25000000000000),(177716748691/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((69/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(39289061707/100000000000000),(-1630856387/50000000000000),(77599403/50000000000000),(-2783227/50000000000000),(50801/20000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((69/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(680046045213/12500000000000),(20924864931/50000000000000),(-42364613/2000000000000),(12217921/25000000000000),(70338473/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((69/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((69/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((69/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel14

namespace Hf4Quad.Panel15
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(71/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((71/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (71/40) (1/40)

def c3 : Certificate := ⟨(311047619047619/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((71/40)+(1/40)*x)) := (SharedCertificates.h2 (71/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((71/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-27452380952381/12500000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((71/40)+(1/40)*x)) := (SharedCertificates.h4 (71/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(5041/1600),(71/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((71/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(190704497354497/50000000000000),(2148783068783/20000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((71/40)+(1/40)*x)) := (SharedCertificates.h8 (71/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((71/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((71/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(357911/64000),(15123/64000),(213/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((71/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(2724203951099537/50000000000000),(230214418402777/100000000000000),(1621228298611/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((71/40)+(1/40)*x)) := (SharedCertificates.h13 (71/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((71/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((71/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(25411681/2560000),(357911/640000),(15123/1280000),(71/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((71/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(346637513640873/12500000000000),(39057748015873/25000000000000),(206290922619/6250000000000),(7748015873/25000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((71/40)+(1/40)*x)) := (SharedCertificates.h18 (71/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((71/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(1761942725585937/100000000000000),(31020118408203/25000000000000),(357911/10240000),(5041/10240000),(347656251/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((71/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(1434841321437807/12500000000000),(404180653926141/50000000000000),(22770741066261/100000000000000),(64142932581/20000000000000),(17694657/781250000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((71/40)+(1/40)*x)) := (SharedCertificates.h22 (71/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((71/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(1563724168957519/50000000000000),(264291408837889/100000000000000),(465301776123/5000000000000),(43690307617/25000000000000),(371298829/20000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((71/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(7022693516461069/100000000000000),(593467057729101/100000000000000),(835869095393/4000000000000),(392426805347/100000000000000),(1042190629/25000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((71/40)+(1/40)*x)) := (SharedCertificates.h26 (71/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((71/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(693902599974899/12500000000000),(68412932391891/12500000000000),(23125498273313/100000000000000),(271426036071/50000000000000),(308428809/4000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((71/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(263462701450787/20000000000000),(25975195917683/20000000000000),(5487717447397/100000000000000),(128819658389/100000000000000),(36595323/2000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((71/40)+(1/40)*x)) := (SharedCertificates.h30 (71/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((71/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((71/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((71/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((71/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((71/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (71/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((71/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((71/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (71/40) (1/40))

def c43 : Certificate := ⟨(12321/1600),(111/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((71/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((71/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(2473515987/4000000000000),(-1114196391/100000000000000),(15056707/100000000000000),(-90431/50000000000000),(2093/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((71/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-41753050347147/4000000000000),(205680661449/100000000000000),(-59002953/3125000000000),(3467533/20000000000000),(35213049/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((71/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((71/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (71/40) (1/40))

def c52 : Certificate := ⟨(31458333333333/25000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((71/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (71/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((71/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (71/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((71/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (71/40) (1/40))

def c56 : Certificate := ⟨(23483365949119/100000000000000),(-45955706359/100000000000000),(89932889/100000000000000),(-87997/50000000000000),(347/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((71/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(3033268101761/50000000000000),(183822825433/100000000000000),(-359731557/100000000000000),(28159/4000000000000),(781/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((71/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((71/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((71/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((71/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((71/40)+(1/40)*x)) := (SharedCertificates.h61 (71/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-87139678539827/100000000000000),(-21658717561/800000000000),(327067087/10000000000000),(-2432909/100000000000000),(23183/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((71/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((71/40)+(1/40)*x)) := (SharedCertificates.h61 (71/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-2255446674889/2500000000000),(-579588783597/20000000000000),(571418831/100000000000000),(5134709/100000000000000),(61501/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((71/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((71/40)+(1/40)*x)) := (SharedCertificates.h67 (71/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-430130633809871/100000000000000),(-13209243629409/100000000000000),(5053333517/25000000000000),(-19063323/50000000000000),(127673/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((71/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((71/40)+(1/40)*x)) := (SharedCertificates.h67 (71/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-90150312973811/20000000000000),(-7229809805711/50000000000000),(3673168987/100000000000000),(3005531/10000000000000),(360317/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((71/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((71/40)+(1/40)*x)) := (SharedCertificates.h72 (71/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(304820647249543/50000000000000),(879780717481/5000000000000),(-62507565053/100000000000000),(2626709/2000000000000),(5989/2500000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((71/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((71/40)+(1/40)*x)) := (SharedCertificates.h72 (71/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(673970411212217/50000000000000),(21489500837771/50000000000000),(-570608711/2500000000000),(-4601177/2500000000000),(15597/1000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((71/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((71/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((71/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(11250110102213/10000000000000),(24371812961/6250000000000),(-425201293/100000000000000),(85413/50000000000000),(7209/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((71/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(1109599900492247/10000000000000),(3349288049649/20000000000000),(-14941912091/20000000000000),(163051331/100000000000000),(1379771/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((71/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(901225747727/100000000000000),(-1360159021/100000000000000),(1624153/20000000000000),(-17329/50000000000000),(243/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((71/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(3036997438953/25000000000000),(184501845261/50000000000000),(-680818567/100000000000000),(837411/50000000000000),(991/3125000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((71/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((71/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((71/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (71/40) (1/40))

def c87 : Certificate := ⟨(20942408376963/100000000000000),(-109646117157/100000000000000),(7175793/1250000000000),(-23481/781250000000),(7911/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((71/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(338132635253/6250000000000),(1169558583/800000000000),(-765417921/100000000000000),(4007423/100000000000000),(29269/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((71/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((71/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((71/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((71/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((71/40)+(1/40)*x)) := (SharedCertificates.h61 (71/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-19374468901617/25000000000000),(-2141639342431/100000000000000),(4965197927/50000000000000),(-2829849/6250000000000),(66889/12500000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((71/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((71/40)+(1/40)*x)) := (SharedCertificates.h61 (71/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-19983610010381/25000000000000),(-568972676741/25000000000000),(4357657113/50000000000000),(-30748947/100000000000000),(69159/10000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((71/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((71/40)+(1/40)*x)) := (SharedCertificates.h67 (71/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-76606620468151/20000000000000),(-2618406520463/25000000000000),(51335361757/100000000000000),(-31903133/12500000000000),(2314783/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((71/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((71/40)+(1/40)*x)) := (SharedCertificates.h67 (71/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-199715555124369/50000000000000),(-2840062033201/25000000000000),(10994116291/25000000000000),(-154460703/100000000000000),(3482457/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((71/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((71/40)+(1/40)*x)) := (SharedCertificates.h72 (71/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(54645311619937/10000000000000),(2830381099123/20000000000000),(-91540478553/100000000000000),(273830349/50000000000000),(208691/5000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((71/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((71/40)+(1/40)*x)) := (SharedCertificates.h72 (71/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(597626608380673/50000000000000),(33829955886101/100000000000000),(-68814630333/50000000000000),(115079277/25000000000000),(2218251/20000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((71/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((71/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((71/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(22222587709279/20000000000000),(15410414139/5000000000000),(-1399926669/100000000000000),(776307/12500000000000),(7943/10000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((71/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5517833623626001/50000000000000),(13554709818591/100000000000000),(-48525494583/50000000000000),(305938449/50000000000000),(14711709/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((71/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(181230545937/20000000000000),(-278248633/25000000000000),(9336031/100000000000000),(-35749/50000000000000),(1447/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((71/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(1083081965033/10000000000000),(293247965767/100000000000000),(-1512067651/100000000000000),(320271/4000000000000),(160719/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((71/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((71/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-59964711628259/25000000000000),(-68654937197/1000000000000),(23818184117/100000000000000),(-114089343/100000000000000),(2354597/12500000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((71/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(28169014084507/50000000000000),(-396746677247/50000000000000),(11175962739/100000000000000),(-78703963/50000000000000),(2248687/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((71/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-135131744514387/100000000000000),(-3929239557/200000000000),(41089396383/100000000000000),(-642999579/100000000000000),(30736927/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((71/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((71/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((71/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((71/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((71/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((71/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((71/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((71/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((71/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((71/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (71/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((71/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((71/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(133255387/1250000000000),(-30029383/5000000000000),(5286863/25000000000000),(-595703/100000000000000),(17007/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((71/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(64517345259281/50000000000000),(-44690459939/6250000000000),(7756617749/100000000000000),(-79225419/100000000000000),(403838883/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((71/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((71/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (71/40) (1/40))

def c134 : Certificate := ⟨(28841/1600),(171/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((71/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((71/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(3003003003003/50000000000000),(-54108162217/100000000000000),(12186523/2500000000000),(-219577/5000000000000),(1597/4000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((71/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(108262012012011/100000000000000),(15422517111/5000000000000),(38996873/4000000000000),(-8783083/100000000000000),(1365009/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((71/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((71/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (71/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((71/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (71/40) (1/40))

def c140 : Certificate := ⟨(24494074162613/100000000000000),(-740231061/4000000000000),(-44509883/100000000000000),(604769/100000000000000),(20693/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((71/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(404740669909/20000000000000),(37011553049/50000000000000),(178039531/100000000000000),(-2419077/100000000000000),(68953/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((71/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((71/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(40953752469/100000000000000),(599203231/20000000000000),(31000093/50000000000000),(16567/10000000000000),(17741/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((71/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((71/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((71/40)+(1/40)*x)) := (SharedCertificates.h144 (71/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(489787464707/100000000000000),(17885151211/50000000000000),(184227879/25000000000000),(940429/50000000000000),(212829/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((71/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((71/40)+(1/40)*x)) := (SharedCertificates.h148 (71/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-70827139272743/25000000000000),(-5181074206509/50000000000000),(-24883271133/100000000000000),(84826541/25000000000000),(48271859/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((71/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((71/40)+(1/40)*x)) := (SharedCertificates.h151 (71/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-286185131315999/50000000000000),(-16520220817/78125000000),(-14632354403/25000000000000),(654193471/100000000000000),(3094319/3125000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((71/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((71/40)+(1/40)*x)) := (SharedCertificates.h154 (71/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(767542713398141/100000000000000),(5529455933111/20000000000000),(12672218293/25000000000000),(-246308239/25000000000000),(66902897/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((71/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((71/40)+(1/40)*x)) := (SharedCertificates.h157 (71/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(535105326155619/25000000000000),(19712979821159/25000000000000),(209799204581/100000000000000),(-2491791927/100000000000000),(92215739/25000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((71/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((71/40)+(1/40)*x)) := (SharedCertificates.h160 (71/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(2211520072294289/100000000000000),(84084531932917/100000000000000),(319791806459/100000000000000),(-2153065733/100000000000000),(399560151/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((71/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(104088360451559/100000000000000),(151042228351/100000000000000),(26129953/6250000000000),(-1168121/25000000000000),(707271/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((71/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((71/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((71/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((71/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((71/40)+(1/40)*x)) := (SharedCertificates.h167 (71/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(54632961388879637/100000000000000),(78295355994473/100000000000000),(197683699777/100000000000000),(-635053793/25000000000000),(188587639/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((71/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(11439980263/6250000000000),(-5246341/2000000000000),(-14319/5000000000000),(987/10000000000000),(259/20000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((71/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(4047959356523/100000000000000),(148106867503/100000000000000),(358444497/100000000000000),(-2401179/50000000000000),(96901/12500000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((71/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((71/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((71/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (71/40) (1/40))

def c175 : Certificate := ⟨(11770631743591/50000000000000),(-51282129093/100000000000000),(-50375253/100000000000000),(48077/2500000000000),(234993/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((71/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(194498201709/10000000000000),(68376172123/100000000000000),(67167003/100000000000000),(-2564107/100000000000000),(352153/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((71/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((71/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(9457387617/25000000000000),(2659808503/100000000000000),(49365781/100000000000000),(-7891/100000000000000),(1103/6250000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((71/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((71/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((71/40)+(1/40)*x)) := (SharedCertificates.h144 (71/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(113120762427/25000000000000),(7940625911/25000000000000),(146695223/25000000000000),(-163527/100000000000000),(42297/20000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((71/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((71/40)+(1/40)*x)) := (SharedCertificates.h148 (71/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-272288681678653/100000000000000),(-149558389557/1562500000000),(-4684972867/50000000000000),(359382749/100000000000000),(12326187/25000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((71/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((71/40)+(1/40)*x)) := (SharedCertificates.h151 (71/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-274945465339211/50000000000000),(-975883866707/5000000000000),(-25716680067/100000000000000),(719085803/100000000000000),(25268383/25000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((71/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((71/40)+(1/40)*x)) := (SharedCertificates.h154 (71/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(147624559372869/20000000000000),(12784608291901/50000000000000),(2328865089/20000000000000),(-494894417/50000000000000),(17090293/12500000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((71/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((71/40)+(1/40)*x)) := (SharedCertificates.h157 (71/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(2056587473607553/100000000000000),(36398498753839/50000000000000),(11091357461/12500000000000),(-2705353803/100000000000000),(376528437/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((71/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((71/40)+(1/40)*x)) := (SharedCertificates.h160 (71/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(530557907749821/25000000000000),(77439189331789/100000000000000),(176291248651/100000000000000),(-2683883193/100000000000000),(407242887/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((71/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(12990974198081/12500000000000),(139412152749/100000000000000),(183699787/100000000000000),(-1027221/20000000000000),(360977/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((71/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((71/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((71/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((71/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((71/40)+(1/40)*x)) := (SharedCertificates.h167 (71/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(54549707275546019/100000000000000),(2892160764783/4000000000000),(79091446011/100000000000000),(-1358238901/50000000000000),(384749949/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((71/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(183319040549/100000000000000),(-15186497/6250000000000),(28137/50000000000000),(4703/50000000000000),(331/25000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((71/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(155618186567/4000000000000),(34201024151/25000000000000),(136204887/100000000000000),(-2552617/50000000000000),(12353/1562500000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((71/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((71/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(10243307963689/100000000000000),(62174112197/20000000000000),(-24475831/3125000000000),(-127749/25000000000000),(35360453/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((71/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(5770877726021/100000000000000),(23464594061/25000000000000),(-88160169/5000000000000),(4909193/20000000000000),(10508657/50000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((71/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((71/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((71/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((71/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((71/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((71/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (71/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((71/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((71/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((71/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (71/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((71/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(19597223171/50000000000000),(-22229361/12500000000000),(1310761/50000000000000),(-629/3125000000000),(217/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((71/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(232824197469841/50000000000000),(-658312319111/50000000000000),(-3088022169/100000000000000),(-5868363/12500000000000),(5055281/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((71/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((71/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((71/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((71/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (71/40) (1/40))

def c223 : Certificate := ⟨(22801/1600),(151/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((71/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2046640561/2560000),(11690571/640000),(186443/1280000),(291/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((71/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((71/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(2254506759/1562500000000),(-1299895789/50000000000000),(17566159/50000000000000),(-42201/10000000000000),(4877/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((71/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(115354124450451/100000000000000),(278597220381/50000000000000),(807455347/50000000000000),(-1089331/12500000000000),(245791/3125000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((71/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((71/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (71/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((71/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (71/40) (1/40))

def c231 : Certificate := ⟨(24075841339557/100000000000000),(-32297560471/100000000000000),(-2514037/5000000000000),(349083/50000000000000),(91713/20000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((71/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(462079330221/12500000000000),(129190241881/100000000000000),(201122957/100000000000000),(-1396333/50000000000000),(1975067/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((71/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((71/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(136651076747/100000000000000),(955138247/10000000000000),(181770747/100000000000000),(313193/100000000000000),(78979/50000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((71/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((71/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((71/40)+(1/40)*x)) := (SharedCertificates.h144 (71/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(1629709938881/100000000000000),(227114701/200000000000),(2142581581/100000000000000),(3234713/100000000000000),(1891027/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((71/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((71/40)+(1/40)*x)) := (SharedCertificates.h148 (71/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-517468605425359/100000000000000),(-4520082659193/25000000000000),(-27928027831/100000000000000),(394043699/100000000000000),(276557201/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((71/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((71/40)+(1/40)*x)) := (SharedCertificates.h151 (71/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-263546655855867/25000000000000),(-37510150435353/100000000000000),(-16349119231/20000000000000),(738520023/100000000000000),(287568669/50000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((71/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((71/40)+(1/40)*x)) := (SharedCertificates.h154 (71/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1384234909170323/100000000000000),(23494861830167/50000000000000),(2978854629/12500000000000),(-1199484969/100000000000000),(382084163/50000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((71/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((71/40)+(1/40)*x)) := (SharedCertificates.h157 (71/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(786527296206447/20000000000000),(139175088805307/100000000000000),(17221887229/6250000000000),(-2890002697/100000000000000),(2134142873/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((71/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((71/40)+(1/40)*x)) := (SharedCertificates.h160 (71/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(4172216778841687/100000000000000),(78050254115159/50000000000000),(121394282023/20000000000000),(-2093821749/100000000000000),(2412138671/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((71/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(107529920360283/100000000000000),(33491483279/12500000000000),(584016661/100000000000000),(-5272139/100000000000000),(1027023/25000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((71/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((71/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((71/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((71/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((71/40)+(1/40)*x)) := (SharedCertificates.h167 (71/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(14101730459759839/25000000000000),(34328415290653/25000000000000),(236726878443/100000000000000),(-1521335577/50000000000000),(2209185503/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((71/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(44320801747/25000000000000),(-431567713/100000000000000),(61313/20000000000000),(10627/100000000000000),(879/12500000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((71/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(7396639708021/100000000000000),(258734046581/100000000000000),(51896193/12500000000000),(-1352389/25000000000000),(4618691/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((71/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((71/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((71/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (71/40) (1/40))

def c259 : Certificate := ⟨(22418389439279/100000000000000),(-42005567089/50000000000000),(71336481/100000000000000),(1959079/100000000000000),(603971/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((71/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(3442147414293/100000000000000),(11201484557/10000000000000),(-95115309/100000000000000),(-2612107/100000000000000),(990763/50000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((71/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((71/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(118483788217/100000000000000),(385571611/5000000000000),(118925237/100000000000000),(-24557/6250000000000),(146627/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((71/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((71/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((71/40)+(1/40)*x)) := (SharedCertificates.h144 (71/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(1413648685299/100000000000000),(18348174009/20000000000000),(700932587/50000000000000),(-616683/12500000000000),(878141/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((71/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((71/40)+(1/40)*x)) := (SharedCertificates.h148 (71/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-60231497266169/12500000000000),(-15677337027423/100000000000000),(13465816323/100000000000000),(183485637/50000000000000),(277459187/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((71/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((71/40)+(1/40)*x)) := (SharedCertificates.h151 (71/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-49019366570397/5000000000000),(-16221769779949/50000000000000),(1998633981/20000000000000),(393301701/50000000000000),(57535633/10000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((71/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((71/40)+(1/40)*x)) := (SharedCertificates.h154 (71/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(129148037732469/10000000000000),(40910781731119/100000000000000),(-35842248311/50000000000000),(-455461887/50000000000000),(383136871/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((71/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((71/40)+(1/40)*x)) := (SharedCertificates.h157 (71/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(3658709443421833/100000000000000),(120470447014251/100000000000000),(-57740807071/100000000000000),(-1463506117/50000000000000),(1068132189/50000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((71/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((71/40)+(1/40)*x)) := (SharedCertificates.h160 (71/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1933065565007063/50000000000000),(33526431017021/25000000000000),(15908346293/10000000000000),(-3493883541/100000000000000),(299372793/12500000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((71/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(107002778616803/100000000000000),(1448382021/625000000000),(-71305381/100000000000000),(-2808563/50000000000000),(4109679/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((71/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((71/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((71/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((71/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((71/40)+(1/40)*x)) := (SharedCertificates.h167 (71/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(56136522775956743/100000000000000),(23795678541073/20000000000000),(-83122730483/100000000000000),(-144977089/5000000000000),(2206130007/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((71/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(7125485873/4000000000000),(-377552267/100000000000000),(531987/50000000000000),(3193/50000000000000),(883/12500000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((71/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(43043848047/625000000000),(224295444857/100000000000000),(-18179783/10000000000000),(-5150787/100000000000000),(4581487/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((71/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((71/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(66511612088051/100000000000000),(2061156947789/100000000000000),(-5714076099/100000000000000),(-73868489/100000000000000),(4380357/10000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((71/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(37471330753831/100000000000000),(633449959967/100000000000000),(-485641129/4000000000000),(129384347/100000000000000),(3733809/12500000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((71/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((71/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((71/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((71/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((71/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((71/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (71/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((71/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(247036487792266637/25000000000000),(4483462346153457/100000000000000),(-45749615777077/100000000000000),0,(32039/25000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((71/40)+(1/40)*x)) := (SharedCertificates.h297 (71/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(10119962529/100000000000000),(-45916771/100000000000000),(338437/50000000000000),(-2599/50000000000000),(59/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((71/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(38822409768599/6250000000000),(423487023989/50000000000000),(3761021371/50000000000000),(1255987/25000000000000),(6697827/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((71/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((71/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (71/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((71/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (71/40) (1/40))

def c307 : Certificate := ⟨(335957026166369/12500000000000),(11091229182759/50000000000000),0,0,(521/50000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((71/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (71/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((71/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (71/40) (1/40))

def c311 : Certificate := ⟨(2087343790668789/100000000000000),(2817541634481/100000000000000),0,0,(521/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((71/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (71/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(1197694414871/25000000000000),(-1293338987/20000000000000),(2182221/25000000000000),(-11783/100000000000000),(21/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((71/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(128759633240361/100000000000000),(44445486587/5000000000000),(-1199869519/100000000000000),(809797/50000000000000),(647/20000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((71/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((71/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (71/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((71/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (71/40) (1/40))

def c316 : Certificate := ⟨(11661545566247/50000000000000),(-48353718669/100000000000000),(82758207/50000000000000),(-70821/12500000000000),(2007/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((71/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(335381773501/5000000000000),(12088429667/6250000000000),(-662065659/100000000000000),(2266269/100000000000000),(573/6250000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((71/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((71/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(224961867993/50000000000000),(1037885179/4000000000000),(57055047/20000000000000),(-2257041/100000000000000),(903/6250000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((71/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((71/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((71/40)+(1/40)*x)) := (SharedCertificates.h144 (71/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(42709810749/800000000000),(306144237119/100000000000000),(3290618739/100000000000000),(-27562053/100000000000000),(2287/1250000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((71/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((71/40)+(1/40)*x)) := (SharedCertificates.h148 (71/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-7333678621101/781250000000),(-1081888860951/4000000000000),(23366674397/25000000000000),(-157333881/50000000000000),(1364103/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((71/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((71/40)+(1/40)*x)) := (SharedCertificates.h151 (71/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-3032973803823/156250000000),(-57786000372917/100000000000000),(36387330633/25000000000000),(-317086939/100000000000000),(918867/20000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((71/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((71/40)+(1/40)*x)) := (SharedCertificates.h154 (71/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1226118763447123/50000000000000),(66834270102841/100000000000000),(-344047703009/100000000000000),(367837303/25000000000000),(6566037/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((71/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((71/40)+(1/40)*x)) := (SharedCertificates.h157 (71/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(7207504397684099/100000000000000),(212311609752449/100000000000000),(-605214410497/100000000000000),(712961653/50000000000000),(8483199/50000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((71/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((71/40)+(1/40)*x)) := (SharedCertificates.h160 (71/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(8009923486485619/100000000000000),(25944856728657/10000000000000),(-50512450029/100000000000000),(-140929819/6250000000000),(4566021/12500000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((71/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(56932597338013/50000000000000),(412776878819/100000000000000),(-1038856083/100000000000000),(2275497/100000000000000),(2049/6250000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((71/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((71/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((71/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((71/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((71/40)+(1/40)*x)) := (SharedCertificates.h167 (71/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(11923570129096661/20000000000000),(206816253227109/100000000000000),(-679985994803/100000000000000),(857468469/50000000000000),(26060531/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((71/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(167734997013/100000000000000),(-581878133/100000000000000),(245731/6250000000000),(-25101/100000000000000),(113/50000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((71/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(16794306151/125000000000),(7771561067/2000000000000),(-255895139/20000000000000),(235093/5000000000000),(67121/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((71/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((71/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((71/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (71/40) (1/40))

def c344 : Certificate := ⟨(80329415943/390625000000),(-112773761121/100000000000000),(385335063/50000000000000),(-2633291/50000000000000),(291/800000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((71/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(1478556506197/25000000000000),(75182507413/50000000000000),(-1027560169/100000000000000),(1755527/25000000000000),(69421/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((71/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((71/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(174890347361/50000000000000),(8892926839/50000000000000),(52275957/50000000000000),(-282447/12500000000000),(20123/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((71/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((71/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((71/40)+(1/40)*x)) := (SharedCertificates.h144 (71/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(415599469491/10000000000000),(1682196459/800000000000),(597978553/50000000000000),(-13422831/50000000000000),(485333/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((71/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((71/40)+(1/40)*x)) := (SharedCertificates.h148 (71/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-165549169710097/20000000000000),(-10516208400503/50000000000000),(144202629289/100000000000000),(-61547087/6250000000000),(1956779/20000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((71/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((71/40)+(1/40)*x)) := (SharedCertificates.h151 (71/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-426234511833679/25000000000000),(-22295374493631/50000000000000),(68281376687/25000000000000),(-1649604947/100000000000000),(6270099/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((71/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((71/40)+(1/40)*x)) := (SharedCertificates.h154 (71/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(2176143129841397/100000000000000),(13172425669777/25000000000000),(-42898702731/10000000000000),(419388701/12500000000000),(7110069/20000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((71/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((71/40)+(1/40)*x)) := (SharedCertificates.h157 (71/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(1584659837337279/25000000000000),(20533951451919/12500000000000),(-6546523379/625000000000),(6537988481/100000000000000),(44906877/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((71/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((71/40)+(1/40)*x)) := (SharedCertificates.h160 (71/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(1739925060515179/25000000000000),(98188123186559/50000000000000),(-839087158159/100000000000000),(1255405631/50000000000000),(157358791/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((71/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((71/40)+(1/40)*x)) := (SharedCertificates.h41 (71/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(56089116372149/50000000000000),(31851588333/10000000000000),(-243821053/12500000000000),(36827/312500000000),(11193/6250000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((71/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((71/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((71/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((71/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((71/40)+(1/40)*x)) := (SharedCertificates.h167 (71/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(58769973183183191/100000000000000),(40146265068999/25000000000000),(-1076688874777/100000000000000),(872097561/12500000000000),(22072617/20000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((71/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(170154918547/100000000000000),(-464937049/100000000000000),(2193857/50000000000000),(-40707/100000000000000),(143/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((71/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(11842272277993/100000000000000),(301785617137/100000000000000),(-1017701127/50000000000000),(6978419/50000000000000),(87663/20000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((71/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((71/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(9813418951063/6250000000000),(900469742679/20000000000000),(-6421023097/50000000000000),(35255833/25000000000000),(5358769/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((71/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(88458987727891/100000000000000),(645316625407/50000000000000),(-25412888713/100000000000000),(218688887/50000000000000),(2046493/12500000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((71/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((71/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(2754586514648437/100000000000000),(45001016845703/25000000000000),(95779/2048000),(6177/10240000),(386718751/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((71/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(36481/1600),(191/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((71/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(6967871/64000),(109443/64000),(573/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((71/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(29990005456890499/10000000000000),(24308052076897039/100000000000000),(84164481448651/10000000000000),(4054873999237/25000000000000),(191219714513/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((71/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(16672221041/50000000000000),(-2702695189/100000000000000),(125485401/100000000000000),(-4389551/100000000000000),(194997/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((71/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2757985786887/50000000000000),(3393490823/10000000000000),(-369195081/20000000000000),(42072823/100000000000000),(64159569/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((71/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((71/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((71/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel15
