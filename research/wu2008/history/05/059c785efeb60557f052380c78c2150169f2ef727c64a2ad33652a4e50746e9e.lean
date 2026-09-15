import MathlibNt.Wu2004MeanValue.AllSourceAP
import MathlibNt.Wu2004MeanValue.ActualOpenIntervals
import MathlibNt.Wu2004MeanValue.APWeightTransferAtoms

/-! The actual two-open-endpoint counting discrepancy, with its aggregate
upper-endpoint atoms paid at the same final modulus level. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

theorem common_profile_open_unit_natural (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ B →
      ∀ (S : Finset ℕ) (f lo hi : ℕ → ℝ) (b : ℕ → ℕ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ 1) →
      (∀ m ∈ S, 2 ≤ lo m / m ∧ lo m < hi m ∧ hi m ≤ x) →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualOpenErrorSum S f lo hi d (b d)|) ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨B₁, J, hB₁, hJ, X₁, hAP⟩ := common_profile_unit_natural A hA
  obtain ⟨E, hE, hatoms⟩ := actualEndpointSum_weighted_log_saving A 1 hA (by norm_num)
  refine ⟨max B₁ (A + 6), 2 * J + E, hB₁.trans_le (le_max_left _ _),
    by positivity, max 3 X₁, ?_⟩
  intro x hx Q hQ S f lo hi b hS hf hr hb
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : X₁ ≤ x := (le_max_right _ _).trans hx
  have hxexp : Real.exp 1 ≤ (x : ℝ) :=
    (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans
      (by exact_mod_cast hx3)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log (x : ℝ) := by linarith
  have hcut (T : ℝ) (hT : T ≤ max B₁ (A + 6)) :
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ T :=
    hQ.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos hlog0 T) (Real.rpow_le_rpow_of_exponent_le hlog1 hT))
  have hlo : ∀ m ∈ S, 0 ≤ lo m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (hS m hm).1
    have h := (le_div_iff₀ hm0).mp (hr m hm).1
    linarith
  have hdomain (m : ℕ) (hm : m ∈ S) :
      (2 ≤ hi m / m ∧ (m : ℝ) * (hi m / m) ≤ x) ∧
        (2 ≤ lo m / m ∧ (m : ℝ) * (lo m / m) ≤ x) := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (hS m hm).1
    have hmul (t : ℝ) : (m : ℝ) * (t / m) = t := by field_simp
    rw [hmul, hmul]
    exact ⟨⟨(hr m hm).1.trans (div_le_div_of_nonneg_right (hr m hm).2.1.le hm0.le),
      (hr m hm).2.2⟩, ⟨(hr m hm).1, (hr m hm).2.1.le.trans (hr m hm).2.2⟩⟩
  have hupper := hAP x hx₁ Q (hcut B₁ (le_max_left _ _)) S f
    (fun m => hi m / m) b hS hf (fun m hm => (hdomain m hm).1) hb
  have hlower := hAP x hx₁ Q (hcut B₁ (le_max_left _ _)) S f
    (fun m => lo m / m) b hS hf (fun m hm => (hdomain m hm).2) hb
  have hE' := hatoms x Q S f (fun _ => hi) b hxexp
    (hcut (A + 6) (le_max_right _ _)) hS hf
  calc
    _ ≤ (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum S f (fun m => hi m / m) d (b d)|) +
        (∑ d ∈ Icc 1 Q, wuModulusWeight d *
          |actualAPSum S f (fun m => lo m / m) d (b d)|) +
        ∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualEndpointSum S f hi d (b d)| :=
      weighted_actualOpenErrorSum_le S f lo hi Q b (fun m hm => (hS m hm).1)
        hlo (fun m hm => (hr m hm).2.1)
    _ ≤ J * x / Real.log (x : ℝ) ^ A + J * x / Real.log (x : ℝ) ^ A +
        E * x / Real.log (x : ℝ) ^ A := add_le_add (add_le_add hupper hlower) hE'
    _ = _ := by ring

end
end Wu2004MeanValue
