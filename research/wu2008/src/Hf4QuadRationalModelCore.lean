import Hf4QuadRatCore
import Hf4QuadModelBasic

/-! Exact rational checks for the arithmetic side conditions of cubic models. -/
namespace Hf4Quad.RationalModel

def Certificate.cubic (p : Certificate) : Cubic :=
  ⟨p.a, p.b, p.c, p.d⟩

def Certificate.Valid (p : Certificate) (f : ℝ → ℝ) : Prop :=
  Model f p.cubic (p.error : ℝ)

@[simp] theorem cast_norm (p : Certificate) : (p.norm : ℝ) = p.cubic.norm := by
  simp [Certificate.norm, Certificate.cubic, Cubic.norm]

@[simp] theorem cast_residual (p q r : Certificate) :
    (residual p q r : ℝ) = mulError p.cubic q.cubic r.cubic := by
  simp [residual, Certificate.cubic, mulError]

theorem Certificate.Valid.add {p q r : Certificate} {f g : ℝ → ℝ}
    (hf : p.Valid f) (hg : q.Valid g) (h : addCondition p q r) :
    r.Valid (fun x => f x+g x) := by
  apply Model.add hf hg
  have hh := (Rat.cast_le (K := ℝ)).mpr h
  simpa [Certificate.cubic] using hh

theorem Certificate.Valid.mul {p q r : Certificate} {f g : ℝ → ℝ}
    (hf : p.Valid f) (hg : q.Valid g) (h : mulCondition p q r) :
    r.Valid (fun x => f x*g x) := by
  apply Model.mul hf hg
  have hh := (Rat.cast_le (K := ℝ)).mpr h
  simpa using hh

theorem Certificate.Valid.inv {p q : Certificate} {f : ℝ → ℝ}
    (hf : p.Valid f) (h : invCondition p q) : q.Valid (fun x => (f x)⁻¹) := by
  apply Model.inv hf (L := (lower p : ℝ))
  · exact Rat.cast_pos.mpr h.1
  · simp [lower, Certificate.cubic]
  · have hh := (Rat.cast_le (K := ℝ)).mpr h.2
    simpa [Certificate.cubic] using hh

theorem Certificate.Valid.neg {p : Certificate} {f : ℝ → ℝ}
    (hf : p.Valid f) : (RationalModel.neg p).Valid (fun x => -f x) := by
  simpa [Certificate.Valid, Certificate.cubic, RationalModel.neg] using Model.neg hf

theorem Certificate.Valid.negTo {p q : Certificate} {f : ℝ → ℝ}
    (hf : p.Valid f) (h : q = RationalModel.neg p) : q.Valid (fun x => -f x) := by
  rw [h]
  exact hf.neg

theorem constant (a : ℚ) : (⟨a,0,0,0,0⟩ : Certificate).Valid (fun _ => (a : ℝ)) := by
  simpa [Certificate.Valid, Certificate.cubic] using Model.constant (a : ℝ)

theorem variableModel (m h : ℚ) :
    (⟨m,h,0,0,0⟩ : Certificate).Valid (fun x => (m : ℝ)+(h : ℝ)*x) := by
  simpa [Certificate.Valid, Certificate.cubic] using Model.variable (m : ℝ) (h : ℝ)

end Hf4Quad.RationalModel
