import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitiveCharacterTransfer
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCofactorFinite
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCofactorMass

namespace MathlibNt.SieveTheory.LiuWeight
open Finset AnalyticNumberTheory.LargeSieve
open scoped BigOperators
noncomputable section

/-- The original whole-source primitive ledger, with the cofactor in both screens. -/
def liuPanPrimitiveCofactorLedger (N A₁ A₂ D m : ℕ) (f : ℕ → ℝ) : ℝ :=
  PanLow.nonprincipalLow (fun a => if a.Coprime m then (f a : ℂ) else 0)
    (fun p => if p.Prime ∧ p.Coprime m then 1 else 0) N A₁ A₂ D

/-- Exact conductor decomposition followed by positive cofactor enlargement.
No source-a triangle and no analytic estimate is used. -/
theorem liuPanActualNonprincipal_sum_le_cofactor (N A₁ A₂ D : ℕ) (f : ℕ → ℝ) :
    (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ * liuPanActualNonprincipalMass N A₁ A₂ q f) ≤
      ∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹ * liuPanPrimitiveCofactorLedger N A₁ A₂ D m f := by
  let F : ℕ → ℕ → ℝ := fun m d =>
    ∑ ψ ∈ PanLow.nonprincipalPrimitiveCharacters d,
      ‖panSourceCharacterAmplitude (fun a => if a.Coprime m then (f a : ℂ) else 0)
        (fun p => if p.Prime ∧ p.Coprime m then 1 else 0) N A₁ A₂ ψ‖
  have hF : ∀ m d, 0 ≤ F m d := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ = ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors, F (q / d) d := by
      apply sum_congr rfl
      intro q hq
      rw [liuPanActualNonprincipalMass_eq_primitive_cofactor N A₁ A₂ q f (mem_Icc.mp hq).1]
    _ ≤ _ := PanCofactor.weighted_sum_divisors_le_rectangle F hF D

/-- A uniform full primitive estimate pays the original same-modulus mass.
The two-log cofactor cost is explicit and is not the printed one-log constant. -/
theorem liuPanActualNonprincipal_sum_le_log_sq
    (N A₁ A₂ D : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hDN : D ≤ N)
    (hinner : ∀ m ∈ Icc 1 D, liuPanPrimitiveCofactorLedger N A₁ A₂ D m f ≤ M) :
    (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ * liuPanActualNonprincipalMass N A₁ A₂ q f) ≤
      M * (1 + Real.log (N : ℝ)) ^ 2 := by
  refine (liuPanActualNonprincipal_sum_le_cofactor N A₁ A₂ D f).trans ?_
  calc
    _ ≤ ∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹ * M :=
      sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hinner m hm) (by positivity)
    _ = M * ∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹ := by rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hDN) hM

end
end MathlibNt.SieveTheory.LiuWeight