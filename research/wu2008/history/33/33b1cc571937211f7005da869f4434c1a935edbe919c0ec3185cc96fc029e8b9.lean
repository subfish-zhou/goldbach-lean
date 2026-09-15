import MathlibNt.Wu2004MeanValue.LargeAP
import MathlibNt.Wu2004MeanValue.APWeightTransferActualAP
import MathlibNt.Wu2004MeanValue.SmallReal
import MathlibNt.Wu2004MeanValue.SourceMasks

/-!
# All-source actual AP distribution on the legal common-profile domain

The Wu weight is transferred at the actual AP-error level. Only afterward
is the small-source producer instantiated, with its own independently chosen
modulus level. No weighted primitive-character majorant is assumed.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

theorem large_actualAP_weighted (A : ℝ) (hA : 0 < A) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀,
      ∀ B : ℝ, b ≤ B →
      ∀ (Q L U : ℕ) (f r : ℕ → ℝ) (a : ℕ → ℕ),
      (U : ℝ) ≤ Real.sqrt x →
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ B →
      Real.log (x : ℝ) ^ (2 * b) ≤ L →
      (∀ m, |f m| ≤ 1) →
      (∀ m ∈ Ioc L U, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      (∀ d ∈ Icc 1 Q, (a d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum (Ioc L U) f r d (a d)|) ≤
        C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨b, J, hb, hJ, X₁, hlarge⟩ :=
    large_actualAP_unweighted (2 * A + 11) (by linarith)
  obtain ⟨C, hC, htransfer⟩ :=
    actualAPSum_weighted_log_saving_of_unweighted A 1 1 J
      (by norm_num) (by norm_num) hJ.le
  refine ⟨b, C, hb, hC, max 3 X₁, ?_⟩
  intro x hx B hB Q L U f r a hU hQ hL hf hr ha
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : X₁ ≤ x := (le_max_right _ _).trans hx
  have hxexp : Real.exp 1 ≤ (x : ℝ) :=
    (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans
      (by exact_mod_cast hx3)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hQroot : (Q : ℝ) ≤ Real.sqrt x :=
    hQ.trans (div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hlog1 (hb.trans hB)))
  apply htransfer x Q (Ioc L U) f r a hxexp hQroot
  · intro m hm
    exact ⟨by have := (mem_Ioc.mp hm).1; omega,
      (by exact_mod_cast (mem_Ioc.mp hm).2 : (m : ℝ) ≤ U).trans hU⟩
  · exact fun m _ => hf m
  · intro m hm
    simpa only [one_mul] using hr m hm
  · exact hlarge x hx₁ B hB Q L U f r a hU hQ hL hf hr ha

/-- All source coordinates up to `sqrt(x)`, actual primes and Wu's exact li.
The profile is common across moduli; every modulus independently selects its
reduced residue. Constants precede the support, coefficients and profile. -/
theorem common_profile_unit_natural (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ B →
      ∀ (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ 1) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ≤
        C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨s, J, hs, hJ, X₁, hlarge⟩ := large_actualAP_weighted A hA
  obtain ⟨Bₛ, Cₛ, hBₛ, hCₛ, x₂, hsmall⟩ :=
    small_real_selected_ebar_log_saving A (2 * s + 1) 1 1 hA
      (by positivity) (by norm_num) (by norm_num)
  let B := max (s + 1) Bₛ
  have hBs : s ≤ B := (by linarith : s ≤ s + 1).trans (le_max_left _ _)
  have hBsmall : Bₛ ≤ B := le_max_right _ _
  refine ⟨B, J + Cₛ, hBₛ.trans_le hBsmall, by positivity,
    max 4 (max X₁ (max ⌈x₂⌉₊ ⌈Real.exp 2⌉₊)), ?_⟩
  intro x hx Q hQ S f r b hS hf hr hb
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx₂ : x₂ ≤ (x : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_left ⌈x₂⌉₊ ⌈Real.exp 2⌉₊).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  have hxexp : Real.exp 2 ≤ (x : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right ⌈x₂⌉₊ ⌈Real.exp 2⌉₊).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  have hlog2 : 2 ≤ Real.log (x : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 2) hxexp
  have hlog0 : 0 < Real.log (x : ℝ) := by linarith
  let L := ⌈Real.log (x : ℝ) ^ (2 * s)⌉₊
  let U := ⌊Real.sqrt (x : ℝ)⌋₊
  obtain ⟨hLlo, hLhi⟩ := ceil_log_source_cutoff (x : ℝ) s hlog2 hs
  have hU : (U : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg _)
  have hSsub : S ⊆ Icc 1 U := fun m hm =>
    mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor (hS m hm).2⟩
  have hQsmall : (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ Bₛ :=
    hQ.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos hlog0 Bₛ)
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hBsmall))
  have hsmall' :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum (S.filter (fun m => m ≤ L)) f r d (b d)|) ≤
          Cₛ * x / Real.log (x : ℝ) ^ A := by
    have h := hsmall x hx₂ Q hQsmall (fun _ => S.filter (fun m => m ≤ L))
      (fun _ => f) (fun _ => r) b
      (fun _ _ m hm => ⟨(hS m (mem_filter.mp hm).1).1,
        (by exact_mod_cast (mem_filter.mp hm).2 : (m : ℝ) ≤ L).trans hLhi⟩)
      (fun _ _ m hm => hf m (mem_filter.mp hm).1)
      (fun _ _ m hm => by simpa only [one_mul] using hr m (mem_filter.mp hm).1) hb
    simpa only [actualAPSum, sum_filter] using h
  obtain ⟨hrExt, hExt⟩ := legal_source_endpoint_extension S f r x hr
    (by exact_mod_cast hx4)
  have hlarge' :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum (Ioc L U) (sourceMask S f) r d (b d)|) ≤
          J * x / Real.log (x : ℝ) ^ A := by
    have h := hlarge x hx₁ B hBs Q L U (sourceMask S f)
      (fun m => if m ∈ S then r m else 2) b hU hQ hLlo
      (abs_sourceMask_le S f 1 (by norm_num) hf)
      (fun m hm => hrExt m
        ((by exact_mod_cast (mem_Ioc.mp hm).2 : (m : ℝ) ≤ U).trans hU)) hb
    simpa only [hExt] using h
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        (|actualAPSum (S.filter (fun m => m ≤ L)) f r d (b d)| +
          |actualAPSum (Ioc L U) (sourceMask S f) r d (b d)|) := by
      apply sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left _ (wuModulusWeight_nonneg d)
      rw [actualAPSum_split_source S f r L U d (b d) hSsub]
      exact abs_add_le _ _
    _ = (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum (S.filter (fun m => m ≤ L)) f r d (b d)|) +
        ∑ d ∈ Icc 1 Q, wuModulusWeight d *
          |actualAPSum (Ioc L U) (sourceMask S f) r d (b d)| := by
      simp only [mul_add, sum_add_distrib]
    _ ≤ Cₛ * x / Real.log (x : ℝ) ^ A + J * x / Real.log (x : ℝ) ^ A :=
      add_le_add hsmall' hlarge'
    _ = _ := by ring

end
end Wu2004MeanValue
