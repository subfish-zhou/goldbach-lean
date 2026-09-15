import SigmaCorrectionLaurentA
import SigmaCorrectionLaurentB
import SigmaCorrectionLaurentC
import SigmaCorrectionPrimitives
namespace SigmaCorrectionFTC
open Real Set MeasureTheory OriginalSigmaStrength SigmaSignedCells
open scoped Interval
noncomputable section

def density (t : ℝ) : ℝ :=
  (-22/189)+
  poleFour (0) (148297720234751447/159040724270459062500) (-451289133137/1379484120656250) (51645526/538440328125) (-1352/84065625) t+
  poleFour (1) (-4/35) (0) (0) (0) t+
  poleFour (2) (-3/20) (0) (0) (0) t+
  poleFour (3) (83248/76545) (-7136/3645) (3968/1701) (1024/2835) t+
  poleFour (5) (-71076470774/24020390625) (1341054884/145578125) (-275166648/13234375) (-1134432/240625) t+
  poleFour (5/3) (-19101750784/45581484375) (-113291264/1302328125) (-46825472/558140625) (4456448/143521875) t+
  (-7903489340/2035338627*t+(6526017140/2035338627))/qA t+
  (5288000/3969*t+(2216000/1323))/qB t^2+
  (235662707120/19931774247*t+(-143667876280/2214641583))/qB t

theorem correctionWeight_density {t : ℝ} (ht : 0<t) : correctionWeight t=density t := by
  have he : correctionWeight t=termA t+termB t+termC t := by
    unfold correctionWeight innerCorrection termA termB termC
    ring
  rw [he,termA_partial ht,termB_partial ht,termC_partial ht]
  unfold density partialA partialB partialC poleFour poleDensity
  ring

/-- Complete primitive of the actual correction, with every forced principal part. -/
def primitive (t : ℝ) : ℝ :=
  (-22/189)*t+
  poleFourPrimitive (0) (148297720234751447/159040724270459062500) (-451289133137/1379484120656250) (51645526/538440328125) (-1352/84065625) t+
  poleFourPrimitive (1) (-4/35) (0) (0) (0) t+
  poleFourPrimitive (2) (-3/20) (0) (0) (0) t+
  poleFourPrimitive (3) (83248/76545) (-7136/3645) (3968/1701) (1024/2835) t+
  poleFourPrimitive (5) (-71076470774/24020390625) (1341054884/145578125) (-275166648/13234375) (-1134432/240625) t+
  poleFourPrimitive (5/3) (-19101750784/45581484375) (-113291264/1302328125) (-46825472/558140625) (4456448/143521875) t+
  quadraticAPrimitive (-7903489340/2035338627) (6526017140/2035338627) t+
  repeatedPrimitive (5288000/3969) (2216000/1323) t+
  SigmaInnerPaid.quadraticPrimitive (235662707120/19931774247) (-143667876280/2214641583) t

theorem primitive_deriv {t : ℝ} (ht : 1≤t) : HasDerivAt primitive (correctionWeight t) t := by
  have ht0 : 0<t := by linarith
  rw [correctionWeight_density ht0]
  have h := (((((((((((hasDerivAt_id t).const_mul (-22/189)).add (poleFourPrimitive_deriv (0) (148297720234751447/159040724270459062500) (-451289133137/1379484120656250) (51645526/538440328125) (-1352/84065625) (by positivity : t+(0)≠0))).add (poleFourPrimitive_deriv (1) (-4/35) (0) (0) (0) (by positivity : t+(1)≠0))).add (poleFourPrimitive_deriv (2) (-3/20) (0) (0) (0) (by positivity : t+(2)≠0))).add (poleFourPrimitive_deriv (3) (83248/76545) (-7136/3645) (3968/1701) (1024/2835) (by positivity : t+(3)≠0))).add (poleFourPrimitive_deriv (5) (-71076470774/24020390625) (1341054884/145578125) (-275166648/13234375) (-1134432/240625) (by positivity : t+(5)≠0))).add (poleFourPrimitive_deriv (5/3) (-19101750784/45581484375) (-113291264/1302328125) (-46825472/558140625) (4456448/143521875) (by positivity : t+(5/3)≠0))).add (quadraticAPrimitive_deriv (-7903489340/2035338627) (6526017140/2035338627) ht)).add (repeatedPrimitive_deriv (5288000/3969) (2216000/1323) ht)).add (SigmaInnerPaid.quadraticPrimitive_deriv (235662707120/19931774247) (-143667876280/2214641583) ht))
  convert h using 1 <;> first | rfl | skip
  unfold density qB
  ring

/-- Full original domain FTC, valid on every original cell, with no new split. -/
theorem correctionMass_ftc {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    correctionMass a b=primitive b-primitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact primitive_deriv (ha.trans ht.1)
  · exact (correctionWeight_continuous (by linarith) hab).intervalIntegrable

end
end SigmaCorrectionFTC
