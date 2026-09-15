import SigmaActualBlockSeparable13
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator13 : ℝ[X] := C ((12598768997428259000000/372417960487462127469)+(-2279130327796216000000/372417960487462127469)*TerminalE.radical)+C ((1972410269527000000/221282210628319743)+(-993729688912000000/853517098137804723)*TerminalE.radical)*X^1

theorem residueNumerator13_degree : residueNumerator13.degree < block13.degree := by
  have hb : block13.degree = (2 : ℕ) := by
    unfold block13
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator13
  compute_degree; all_goals norm_num

def simplePartPrimitive13 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator13 block13

theorem simplePartPrimitive13_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive13 (residueNumerator13.eval t / block13.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block13_separable
    residueNumerator13_degree t (block13_eval_ne ht)

end SigmaActualBlockSeparable
