import Hf4QuadModel

noncomputable section
namespace Hf4Quad
theorem Model.neg {f : ℝ → ℝ} {p : Cubic} {e : ℝ} (hf : Model f p e) :
    Model (fun x => -f x) ⟨-p.a,-p.b,-p.c,-p.d⟩ e := by
  intro x hx
  have he : -f x-Cubic.eval ⟨-p.a,-p.b,-p.c,-p.d⟩ x = -(f x-p.eval x) := by
    simp only [Cubic.eval]
    ring
  rw [he,abs_neg]
  exact hf x hx

theorem Model.constant (a : ℝ) : Model (fun _ => a) ⟨a,0,0,0⟩ 0 := by
  intro x _
  simp [Cubic.eval]

theorem Model.variable (m h : ℝ) : Model (fun x => m+h*x) ⟨m,h,0,0⟩ 0 := by
  intro x _
  simp [Cubic.eval]

end Hf4Quad
