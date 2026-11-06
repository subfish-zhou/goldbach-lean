import MathlibNt.Wu2004MeanValue.ActualAP

/-! Consumption of the proved principal estimate in the actual AP expansion. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve

noncomputable section


theorem principal_selected_unweighted_log_saving (A F K : ℝ)
    (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀,
      ∀ (Q : ℕ) (S : ℕ → Finset ℕ) (f r : ℕ → ℕ → ℝ),
      Q ≤ x →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, |f d m| ≤ F) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d,
        2 ≤ r d m ∧ (m : ℝ) * r d m ≤ K * x) →
      (∑ d ∈ Icc 1 Q,
        |coprimePrincipalSum ((S d).filter (fun m => m.Coprime d)) (f d) (r d) d| /
          d.totient) ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨J, hJ, x₁, hbound⟩ :=
    coprimePrincipalSum_log_saving (A + 2) F K (by linarith) hF
  refine ⟨4 * J, by positivity, max ⌈x₁⌉₊ ⌈Real.exp 1⌉₊, ?_⟩
  intro x hx Q S f r hQ hS hf hr
  have hx₁ : x₁ ≤ (x : ℝ) := (Nat.le_ceil x₁).trans
    (by exact_mod_cast (le_max_left ⌈x₁⌉₊ ⌈Real.exp 1⌉₊).trans hx)
  have hxexp : Real.exp 1 ≤ (x : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right ⌈x₁⌉₊ ⌈Real.exp 1⌉₊).trans hx)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log (x : ℝ) := by linarith
  have hmass := PanCofactor.reciprocal_totient_mass_le_log_sq hQ
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
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (J * x / Real.log (x : ℝ) ^ (A + 2)) *
        (4 * Real.log (x : ℝ) ^ (2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.rpow_two]
      nlinarith
    _ = _ := by
      rw [Real.rpow_add hlog0]
      field_simp

end
end Wu2004MeanValue
