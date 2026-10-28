import Hf4QuadRationalModelCore
namespace Hf4Quad.RationalModel
theorem Certificate.Valid.addExact {p q : Certificate} {f g : ℝ → ℝ}
    (hf : p.Valid f) (hg : q.Valid g) :
    (RationalModel.addExact p q).Valid (fun x => f x+g x) := by
  apply hf.add hg
  simp [addCondition, RationalModel.addExact]
theorem Certificate.Valid.scale {p : Certificate} {f : ℝ → ℝ}
    (hf : p.Valid f) (s : ℚ) :
    (RationalModel.scale s p).Valid (fun x => (s : ℝ)*f x) := by
  apply (constant s).mul hf
  simp [mulCondition, residual, Certificate.norm, RationalModel.scale, mul_comm]
end Hf4Quad.RationalModel
