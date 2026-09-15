import MathlibNt.Wu2004MeanValue.ActualAP

/-! Consumption of the proved principal estimate in the actual AP expansion. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve

noncomputable section

theorem coprimePrincipalSum_div_le_principalModulusSup (F K : ℝ) (hF : 0 ≤ F) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (d : ℕ) (S : Finset ℕ) (f r : ℕ → ℝ),
      0 < d → (d : ℝ) ≤ x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      |coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d| / d.totient ≤
        principalModulusSup x F K d := by
  obtain ⟨C, hC, x₀, hbound⟩ := coprimePrincipalSum_log_saving 1 F K (by norm_num) hF
  refine ⟨max 2 x₀, ?_⟩
  intro x hx d S f r hd hdx hS hf hr
  have hx₀ := (le_max_right 2 x₀).trans hx
  have hx2 := (le_max_left 2 x₀).trans hx
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  unfold principalModulusSup
  apply le_csSup
  · refine ⟨(C * x / Real.log x ^ (1 : ℝ)) / d.totient, ?_⟩
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · have hx0 : 0 ≤ x := by linarith
      positivity
    · obtain ⟨T, g, t, hT, hg, ht, rfl⟩ := hv
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact hbound x hx₀ d (T.filter (fun m => m.Coprime d)) g t hd hdx
        (fun m hm => hT m (mem_filter.mp hm).1)
        (fun m hm => hg m (mem_filter.mp hm).1)
        (fun m hm => ht m (mem_filter.mp hm).1)
  · exact Set.mem_insert_of_mem _ ⟨S, f, r, hS, hf, hr, rfl⟩

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
