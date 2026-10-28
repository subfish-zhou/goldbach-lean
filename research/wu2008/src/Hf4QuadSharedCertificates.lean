import Hf4QuadRationalModel
import Hf4QuadCompactDag
import Hf4QuadExactOperations
noncomputable section
namespace Hf4Quad.SharedCertificates
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c1 : Certificate := ⟨(1549193338483/400000000000),0,0,0,(1/2000000000000)⟩
theorem h1 (m h : ℝ) : c1.Valid (fun x => f1 (m+h*x)) := by
  convert radical using 1 <;> norm_num [Certificate.Valid,Certificate.cubic,c1,f1]

def c2 : Certificate := ⟨(184/105),0,0,0,0⟩
theorem h2 (m h : ℝ) : c2.Valid (fun x => f2 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c2,f2] using constant ((184/105))

def c4 : Certificate := ⟨(32/35),0,0,0,0⟩
theorem h4 (m h : ℝ) : c4.Valid (fun x => f4 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c4,f4] using constant ((32/35))

def c8 : Certificate := ⟨(1144/945),0,0,0,0⟩
theorem h8 (m h : ℝ) : c8.Valid (fun x => f8 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c8,f8] using constant ((1144/945))

def c13 : Certificate := ⟨(5261/540),0,0,0,0⟩
theorem h13 (m h : ℝ) : c13.Valid (fun x => f13 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c13,f13] using constant ((5261/540))

def c18 : Certificate := ⟨(176/63),0,0,0,0⟩
theorem h18 (m h : ℝ) : c18.Valid (fun x => f18 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c18,f18] using constant ((176/63))

def c22 : Certificate := ⟨(1759/270),0,0,0,0⟩
theorem h22 (m h : ℝ) : c22.Valid (fun x => f22 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c22,f22] using constant ((1759/270))

def c26 : Certificate := ⟨(2122/945),0,0,0,0⟩
theorem h26 (m h : ℝ) : c26.Valid (fun x => f26 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c26,f26] using constant ((2122/945))

def c30 : Certificate := ⟨(299/1260),0,0,0,0⟩
theorem h30 (m h : ℝ) : c30.Valid (fun x => f30 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c30,f30] using constant ((299/1260))

def c33 : Certificate := ⟨2145,0,0,0,0⟩
theorem h33 (m h : ℝ) : c33.Valid (fun x => f33 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c33,f33] using constant (2145)

def c35 : Certificate := ⟨4418,0,0,0,0⟩
theorem h35 (m h : ℝ) : c35.Valid (fun x => f35 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c35,f35] using constant (4418)

def c38 : Certificate := ⟨2280,0,0,0,0⟩
theorem h38 (m h : ℝ) : c38.Valid (fun x => f38 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c38,f38] using constant (2280)

def c41 : Certificate := ⟨1,0,0,0,0⟩
theorem h41 (m h : ℝ) : c41.Valid (fun x => f41 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c41,f41] using constant (1)

def c44 : Certificate := ⟨210,0,0,0,0⟩
theorem h44 (m h : ℝ) : c44.Valid (fun x => f44 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c44,f44] using constant (210)

def c48 : Certificate := ⟨2,0,0,0,0⟩
theorem h48 (m h : ℝ) : c48.Valid (fun x => f48 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c48,f48] using constant (2)

def c50 : Certificate := ⟨3,0,0,0,0⟩
theorem h50 (m h : ℝ) : c50.Valid (fun x => f50 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c50,f50] using constant (3)

def c51 : Certificate := ⟨(33333333333333/100000000000000),0,0,0,(1/100000000000000)⟩
theorem h51 (m h : ℝ) : c51.Valid (fun x => f51 (m+h*x)) := by
  exact (h50 m h).inv (by decide +kernel)

def c53 : Certificate := RationalModel.neg c41
theorem h53 (m h : ℝ) : c53.Valid (fun x => f53 (m+h*x)) := by
  exact (h41 m h).neg

def c59 : Certificate := ⟨6,0,0,0,0⟩
theorem h59 (m h : ℝ) : c59.Valid (fun x => f59 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c59,f59] using constant (6)

def c61 : Certificate := ⟨-14,0,0,0,0⟩
theorem h61 (m h : ℝ) : c61.Valid (fun x => f61 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c61,f61] using constant (-14)

def c67 : Certificate := ⟨-70,0,0,0,0⟩
theorem h67 (m h : ℝ) : c67.Valid (fun x => f67 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c67,f67] using constant (-70)

def c72 : Certificate := ⟨105,0,0,0,0⟩
theorem h72 (m h : ℝ) : c72.Valid (fun x => f72 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c72,f72] using constant (105)

def c116 : Certificate := ⟨10,0,0,0,0⟩
theorem h116 (m h : ℝ) : c116.Valid (fun x => f116 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c116,f116] using constant (10)

def c118 : Certificate := ⟨18,0,0,0,0⟩
theorem h118 (m h : ℝ) : c118.Valid (fun x => f118 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c118,f118] using constant (18)

def c127 : Certificate := ⟨64,0,0,0,0⟩
theorem h127 (m h : ℝ) : c127.Valid (fun x => f127 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c127,f127] using constant (64)

def c129 : Certificate := ⟨945,0,0,0,0⟩
theorem h129 (m h : ℝ) : c129.Valid (fun x => f129 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c129,f129] using constant (945)

def c144 : Certificate := ⟨12,0,0,0,0⟩
theorem h144 (m h : ℝ) : c144.Valid (fun x => f144 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c144,f144] using constant (12)

def c148 : Certificate := ⟨-140,0,0,0,0⟩
theorem h148 (m h : ℝ) : c148.Valid (fun x => f148 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c148,f148] using constant (-140)

def c151 : Certificate := ⟨-280,0,0,0,0⟩
theorem h151 (m h : ℝ) : c151.Valid (fun x => f151 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c151,f151] using constant (-280)

def c154 : Certificate := ⟨385,0,0,0,0⟩
theorem h154 (m h : ℝ) : c154.Valid (fun x => f154 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c154,f154] using constant (385)

def c157 : Certificate := ⟨1050,0,0,0,0⟩
theorem h157 (m h : ℝ) : c157.Valid (fun x => f157 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c157,f157] using constant (1050)

def c160 : Certificate := ⟨525,0,0,0,0⟩
theorem h160 (m h : ℝ) : c160.Valid (fun x => f160 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c160,f160] using constant (525)

def c167 : Certificate := ⟨5,0,0,0,0⟩
theorem h167 (m h : ℝ) : c167.Valid (fun x => f167 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c167,f167] using constant (5)

def c205 : Certificate := ⟨-5,0,0,0,0⟩
theorem h205 (m h : ℝ) : c205.Valid (fun x => f205 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c205,f205] using constant (-5)

def c207 : Certificate := ⟨21,0,0,0,0⟩
theorem h207 (m h : ℝ) : c207.Valid (fun x => f207 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c207,f207] using constant (21)

def c210 : Certificate := ⟨26,0,0,0,0⟩
theorem h210 (m h : ℝ) : c210.Valid (fun x => f210 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c210,f210] using constant (26)

def c212 : Certificate := ⟨250,0,0,0,0⟩
theorem h212 (m h : ℝ) : c212.Valid (fun x => f212 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c212,f212] using constant (250)

def c216 : Certificate := ⟨189,0,0,0,0⟩
theorem h216 (m h : ℝ) : c216.Valid (fun x => f216 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c216,f216] using constant (189)

def c225 : Certificate := ⟨90,0,0,0,0⟩
theorem h225 (m h : ℝ) : c225.Valid (fun x => f225 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c225,f225] using constant (90)

def c289 : Certificate := ⟨-11,0,0,0,0⟩
theorem h289 (m h : ℝ) : c289.Valid (fun x => f289 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c289,f289] using constant (-11)

def c291 : Certificate := ⟨97,0,0,0,0⟩
theorem h291 (m h : ℝ) : c291.Valid (fun x => f291 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c291,f291] using constant (97)

def c294 : Certificate := ⟨108,0,0,0,0⟩
theorem h294 (m h : ℝ) : c294.Valid (fun x => f294 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c294,f294] using constant (108)

def c297 : Certificate := ⟨(292797540973287/400000000000),0,0,0,(189/2000000000000)⟩
theorem h297 (m h : ℝ) : c297.Valid (fun x => f297 (m+h*x)) := by
  exact (h216 m h).mul (h1 m h) (by decide +kernel)

def c301 : Certificate := ⟨9,0,0,0,0⟩
theorem h301 (m h : ℝ) : c301.Valid (fun x => f301 (m+h*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c301,f301] using constant (9)

def c303 : Certificate := ⟨(1549193338483/200000000000),0,0,0,(1/1000000000000)⟩
theorem h303 (m h : ℝ) : c303.Valid (fun x => f303 (m+h*x)) := by
  exact (h48 m h).mul (h1 m h) (by decide +kernel)

def c304 : Certificate := RationalModel.neg c303
theorem h304 (m h : ℝ) : c304.Valid (fun x => f304 (m+h*x)) := by
  exact (h303 m h).neg

def c306 : Certificate := RationalModel.addExact c167 c1
theorem h306 (m h : ℝ) : c306.Valid (fun x => f306 (m+h*x)) := by
  exact (h167 m h).addExact (h1 m h)

def c309 : Certificate := RationalModel.neg c1
theorem h309 (m h : ℝ) : c309.Valid (fun x => f309 (m+h*x)) := by
  exact (h1 m h).neg

def c310 : Certificate := RationalModel.addExact c167 c309
theorem h310 (m h : ℝ) : c310.Valid (fun x => f310 (m+h*x)) := by
  exact (h167 m h).addExact (h309 m h)
end Hf4Quad.SharedCertificates
