import MathlibNt.Wu2004MeanValue.BalancedPrincipalSelected
import MathlibNt.Wu2004MeanValue.BalancedPrimitive

/-! Actual unweighted AP distribution for the common balanced profile. -/

namespace Wu2004MeanValue
open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
noncomputable section

theorem balanced_large_actualAP_unweighted (A eta : ℝ)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀,
      ∀ B : ℝ, b ≤ B →
      ∀ (Q L U : ℕ) (f r : ℕ → ℝ) (a : ℕ → ℕ),
      (U : ℝ) ≤ (x : ℝ) ^ (1 - eta) →
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ B →
      Real.log (x : ℝ) ^ (2 * b) ≤ L →
      (∀ m, |f m| ≤ 1) →
      (∀ m ∈ Ioc L U, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      (∀ d ∈ Icc 1 Q, (a d).Coprime d) →
      (∑ d ∈ Icc 1 Q, |actualAPSum (Ioc L U) f r d (a d)|) ≤
        C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨b, J, hb, hJ, X₁, hprimitive⟩ :=
    balanced_commonPrimitiveSource_log_saving_uniform_level (A + 2) eta (by linarith) heta
  obtain ⟨P, hP, X₂, hprincipal⟩ :=
    balanced_principal_selected_unweighted_log_saving A eta 1 hA heta (by norm_num)
  refine ⟨b, P + 4 * J, hb, by positivity, max 3 (max X₁ X₂), ?_⟩
  intro x hx B hB Q L U f r a hU hQ hL hf hr ha
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx₂ : X₂ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    apply le_of_lt
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).trans_le
      (by exact_mod_cast hx3)
  have hlog0 : 0 < Real.log (x : ℝ) := by linarith
  have hQroot : (Q : ℝ) ≤ Real.sqrt x := by
    refine hQ.trans ?_
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hlog0 B)).mpr
    have hpow := Real.one_le_rpow hlog1 (hb.trans hB)
    nlinarith [Real.sqrt_nonneg (x : ℝ)]
  have hrootx : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hxR (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hQx : Q ≤ x := by exact_mod_cast hQroot.trans hrootx
  have hS : ∀ m ∈ Ioc L U, 1 ≤ m ∧ (m : ℝ) ≤ (x : ℝ) ^ (1 - eta) := by
    intro m hm
    exact ⟨by have := (mem_Ioc.mp hm).1; omega,
      (by exact_mod_cast (mem_Ioc.mp hm).2 : (m : ℝ) ≤ U).trans hU⟩
  have hprim (h : ℕ) (hh : h ∈ Icc 1 Q) :
      cofactorLedger (Ioc L U) f r h Q ≤ J * x / Real.log (x : ℝ) ^ (A + 2) := by
    rw [cofactorLedger_interval]
    apply hprimitive x hx₁ B hB h Q L U (fun m => (f m : ℂ)) r
      (mem_Icc.mp hh).1 ((mem_Icc.mp hh).2.trans hQx) hU hQ hL
    · intro m
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hf m
    · intro m hm
      exact ⟨by have := (hr m hm).1; linarith, (hr m hm).2⟩
  have hcofactor :
      (∑ h ∈ Icc 1 Q, (h.totient : ℝ)⁻¹ * cofactorLedger (Ioc L U) f r h Q) ≤
        (4 * J) * x / Real.log (x : ℝ) ^ A := by
    calc
      _ ≤ ∑ h ∈ Icc 1 Q, (h.totient : ℝ)⁻¹ *
          (J * x / Real.log (x : ℝ) ^ (A + 2)) :=
        sum_le_sum fun h hh => mul_le_mul_of_nonneg_left (hprim h hh) (by positivity)
      _ = (J * x / Real.log (x : ℝ) ^ (A + 2)) *
          ∑ h ∈ Icc 1 Q, (h.totient : ℝ)⁻¹ := by rw [← sum_mul, mul_comm]
      _ ≤ (J * x / Real.log (x : ℝ) ^ (A + 2)) * (1 + Real.log (x : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hQx)
          (by positivity)
      _ ≤ (J * x / Real.log (x : ℝ) ^ (A + 2)) *
          (4 * Real.log (x : ℝ) ^ (2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Real.rpow_two]
        nlinarith
      _ = _ := by rw [Real.rpow_add hlog0]; field_simp
  have hprincipal' := hprincipal x hx₂ Q (fun _ => Ioc L U) (fun _ => f) (fun _ => r)
    hQx (fun _ _ => hS) (fun _ _ m _ => hf m) (fun _ _ m hm => hr m hm)
  calc
    _ ≤ (∑ d ∈ Icc 1 Q,
        |coprimePrincipalSum ((Ioc L U).filter (fun m => m.Coprime d)) f r d| / d.totient) +
        ∑ h ∈ Icc 1 Q, (h.totient : ℝ)⁻¹ * cofactorLedger (Ioc L U) f r h Q :=
      sum_abs_actualAP_le_principal_add_cofactor _ _ _ _ _ (fun m hm => (hS m hm).1) ha
    _ ≤ P * x / Real.log (x : ℝ) ^ A + (4 * J) * x / Real.log (x : ℝ) ^ A :=
      add_le_add hprincipal' hcofactor
    _ = _ := by ring

end
end Wu2004MeanValue