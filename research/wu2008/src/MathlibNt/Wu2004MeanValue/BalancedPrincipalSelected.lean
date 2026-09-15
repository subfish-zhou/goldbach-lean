import MathlibNt.Wu2004MeanValue.BalancedPrincipal
import MathlibNt.Wu2004MeanValue.ActualAP

/-!
# Modulus-selected balanced principal errors

The support may be selected separately for every modulus. In particular,
the cofactor coprimality mask is applied before the inner absolute value.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve

noncomputable section

theorem balanced_principal_selected_unweighted_log_saving (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀,
      ∀ (Q : ℕ) (S : ℕ → Finset ℕ) (f r : ℕ → ℕ → ℝ),
      Q ≤ x →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 1 ≤ m ∧ (m : ℝ) ≤ (x : ℝ) ^ (1 - eta)) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, |f d m| ≤ F) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d,
        2 ≤ r d m ∧ (m : ℝ) * r d m ≤ x) →
      (∑ d ∈ Icc 1 Q,
        |coprimePrincipalSum ((S d).filter (fun m => m.Coprime d)) (f d) (r d) d| /
          d.totient) ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨J, hJ, x₁, hbound⟩ :=
    balanced_coprimePrincipalSum_log_saving (A + 2) eta F (by linarith) heta hF
  refine ⟨4 * J, by positivity, max ⌈x₁⌉₊ ⌈Real.exp 1⌉₊, ?_⟩
  intro x hx Q S f r hQ hS hf hr
  have hx₁ : x₁ ≤ (x : ℝ) := (Nat.le_ceil x₁).trans
    (by exact_mod_cast (le_max_left ⌈x₁⌉₊ ⌈Real.exp 1⌉₊).trans hx)
  have hxexp : Real.exp 1 ≤ (x : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right ⌈x₁⌉₊ ⌈Real.exp 1⌉₊).trans hx)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log (x : ℝ) := by linarith
  calc
    _ ≤ ∑ d ∈ Icc 1 Q,
        (J * x / Real.log (x : ℝ) ^ (A + 2)) / d.totient := by
      apply sum_le_sum
      intro d hd
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply hbound x hx₁ d ((S d).filter (fun m => m.Coprime d)) (f d) (r d)
        (mem_Icc.mp hd).1 (by exact_mod_cast (mem_Icc.mp hd).2.trans hQ)
      · exact fun m hm => hS d hd m (mem_filter.mp hm).1
      · exact fun m hm => hf d hd m (mem_filter.mp hm).1
      · exact fun m hm => hr d hd m (mem_filter.mp hm).1
    _ = (J * x / Real.log (x : ℝ) ^ (A + 2)) *
        ∑ d ∈ Icc 1 Q, (d.totient : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, mul_sum]
    _ ≤ (J * x / Real.log (x : ℝ) ^ (A + 2)) *
        (1 + Real.log (x : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hQ)
        (by positivity)
    _ ≤ (J * x / Real.log (x : ℝ) ^ (A + 2)) *
        (4 * Real.log (x : ℝ) ^ (2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.rpow_two]
      nlinarith
    _ = _ := by rw [Real.rpow_add hlog0]; field_simp

theorem balanced_principal_error_selected_weighted (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ (Q : ℕ) (S : ℕ → Finset ℕ) (f r : ℕ → ℕ → ℝ),
      (Q : ℝ) ≤ x →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 1 ≤ m ∧ (m : ℝ) ≤ x ^ (1 - eta)) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, |f d m| ≤ F) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d,
        2 ≤ r d m ∧ (m : ℝ) * r d m ≤ x) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |∑ m ∈ S d, f d m * principalError (r d m)| / d.totient) ≤
          C * x / Real.log x ^ A := by
  obtain ⟨J, hJ, x₁, hcore⟩ :=
    balanced_principal_moving_sum_bound (A + 6) eta F (by linarith) heta hF
  obtain ⟨L, hL, hweight⟩ := wu_reciprocal_totient_sum_bound
  refine ⟨J * L, by positivity, max 2 x₁, ?_⟩
  intro x hx Q S f r hQ hS hf hr
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : x₁ ≤ x := (le_max_right _ _).trans hx
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        (J * x / Real.log x ^ (A + 6)) / d.totient := by
      apply sum_le_sum
      intro d hd
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (hcore x hx₁ (S d) (f d) (r d) (hS d hd) (hf d hd) (hr d hd))
        (wuModulusWeight_nonneg d)
    _ = (J * x / Real.log x ^ (A + 6)) *
        (∑ d ∈ Icc 1 Q, wuModulusWeight d / d.totient) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (J * x / Real.log x ^ (A + 6)) * (L * Real.log x ^ (6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hweight x hx2 Q hQ) (by positivity)
    _ = _ := by rw [Real.rpow_add hlog0]; field_simp

end
end Wu2004MeanValue