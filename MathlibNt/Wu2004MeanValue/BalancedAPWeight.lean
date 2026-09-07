import MathlibNt.Wu2004MeanValue.BalancedAPWeightCount

/-! Wu's exact modulus weight, paid using the product-fiber envelope. -/

namespace Wu2004MeanValue
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.Richert1969
noncomputable section

def balancedAPEnvelopeConstant (F : ℝ) : ℝ :=
  F * (2 / Real.log 2 + liuPanLiEnvelopeConstant 0) * richertReciprocalTotientConstant

theorem balancedAPEnvelopeConstant_nonneg {F : ℝ} (hF : 0 ≤ F) :
    0 ≤ balancedAPEnvelopeConstant F := by
  unfold balancedAPEnvelopeConstant
  positivity [liuPanLiEnvelopeConstant_nonneg 0, richertReciprocalTotientConstant_pos]

theorem balanced_modulus_mul_actualAPError_le (x F : ℝ) (S : Finset ℕ)
    (f r : ℕ → ℝ) (d b : ℕ)
    (hx : 2 ≤ x) (hF : 0 ≤ F) (hd : 0 < d) (hdx : (d : ℝ) ≤ x)
    (hS : ∀ m ∈ S, 0 < m) (hf : ∀ m ∈ S, |f m| ≤ F)
    (hr : ∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x) :
    (d : ℝ) * actualAPError S f r d b ≤
      balancedAPEnvelopeConstant F * x * (1 + Real.log x) ^ 2 := by
  let T := S.filter (fun m => m.Coprime d)
  have hT : ∀ m ∈ T, m ∈ S := fun m hm => (mem_filter.mp hm).1
  have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hC : 0 ≤ liuPanLiEnvelopeConstant 0 := liuPanLiEnvelopeConstant_nonneg 0
  have hmass : (∑ m ∈ T, r m) ≤ x * (1 + Real.log x) := by
    calc
      _ ≤ ∑ m ∈ T, x * (1 / (m : ℝ)) := by
        apply sum_le_sum
        intro m hm
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hS m (hT m hm)
        have h := (le_div_iff₀ hm0).mpr (by
          simpa only [mul_comm] using (hr m (hT m hm)).2)
        simpa only [mul_one_div] using h
      _ = x * (∑ m ∈ T, 1 / (m : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ap_source_reciprocal_bound x T hx (by
        intro m hm
        refine ⟨hS m (hT m hm), ?_⟩
        have hp := hr m (hT m hm)
        have hm0 := Nat.cast_nonneg (α := ℝ) m
        nlinarith)) (by linarith)
  have hcount := balanced_scaledPrimeCount_sum_bound x T r d b hx hdx
    (fun m hm => hS m (hT m hm))
    (fun m hm => ⟨by have := (hr m (hT m hm)).1; linarith, (hr m (hT m hm)).2⟩)
  have htot :
      (d.totient : ℝ) * actualAPError S f r d b ≤
      F * (2 / Real.log 2 + liuPanLiEnvelopeConstant 0) * x * (1 + Real.log x) := by
    calc
      _ ≤ (d.totient : ℝ) *
          ∑ m ∈ T, |f m * ebar ((m : ℝ) * r m) d b m| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hphi.le
      _ ≤ ∑ m ∈ T, F *
          ((d : ℝ) * scaledPrimeCount ((m : ℝ) * r m) d b m +
            liuPanLiEnvelopeConstant 0 * r m) := by
        rw [mul_sum]
        apply sum_le_sum
        intro m hm
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (hS m (hT m hm)).ne'
        have he : (d.totient : ℝ) * |ebar ((m : ℝ) * r m) d b m| ≤
            (d : ℝ) * scaledPrimeCount ((m : ℝ) * r m) d b m +
              liuPanLiEnvelopeConstant 0 * r m := by
          unfold ebar
          rw [mul_div_cancel_left₀ _ hm0]
          calc
            _ ≤ (d.totient : ℝ) *
                (|(scaledPrimeCount ((m : ℝ) * r m) d b m : ℝ)| +
                  |wuLi (r m) / d.totient|) :=
              mul_le_mul_of_nonneg_left (abs_sub _ _) hphi.le
            _ = (d.totient : ℝ) * scaledPrimeCount ((m : ℝ) * r m) d b m +
                |wuLi (r m)| := by
              rw [abs_of_nonneg (by positivity), abs_div, abs_of_pos hphi, mul_add]
              field_simp
            _ ≤ _ := add_le_add
              (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le d) (by positivity))
              (wuLi_abs_le_linear (hr m (hT m hm)).1)
        rw [abs_mul, mul_left_comm]
        exact mul_le_mul (hf m (hT m hm)) he
          (mul_nonneg hphi.le (abs_nonneg _)) hF
      _ = F * ((d : ℝ) * (∑ m ∈ T, (scaledPrimeCount ((m : ℝ) * r m) d b m : ℝ)) +
          liuPanLiEnvelopeConstant 0 * ∑ m ∈ T, r m) := by
        simp only [mul_add, sum_add_distrib, ← mul_sum]
      _ ≤ F * ((2 / Real.log 2) * x * Real.log x +
          liuPanLiEnvelopeConstant 0 * (x * (1 + Real.log x))) :=
        mul_le_mul_of_nonneg_left (add_le_add hcount
          (mul_le_mul_of_nonneg_left hmass hC)) hF
      _ ≤ _ := by
        have h := mul_nonneg hF (show 0 ≤ (2 / Real.log 2) * x by positivity)
        nlinarith
  calc
    _ = ((d : ℝ) / d.totient) * ((d.totient : ℝ) * actualAPError S f r d b) := by
      field_simp
    _ ≤ (richertReciprocalTotientConstant * Real.log x) *
        (F * (2 / Real.log 2 + liuPanLiEnvelopeConstant 0) * x * (1 + Real.log x)) :=
      mul_le_mul (ap_totient_ratio_le_log x d hx hd hdx) htot
        (mul_nonneg hphi.le (actualAPError_nonneg ..))
        (mul_nonneg richertReciprocalTotientConstant_pos.le hlog)
    _ ≤ _ := by
      unfold balancedAPEnvelopeConstant
      have h := mul_nonneg
        (mul_nonneg (mul_nonneg hF (show 0 ≤ 2 / Real.log 2 +
          liuPanLiEnvelopeConstant 0 by positivity)) richertReciprocalTotientConstant_pos.le)
        (show 0 ≤ x * (1 + Real.log x) by positivity)
      nlinarith

theorem balanced_actualAP_weighted_log_saving_of_unweighted (A F U : ℝ)
    (hF : 0 ≤ F) (hU : 0 ≤ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (Q : ℕ)
      (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      Real.exp 1 ≤ x → (Q : ℝ) ≤ x →
      (∀ m ∈ S, 0 < m) → (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      (∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) ≤
        U * x / Real.log x ^ (2 * A + 11) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨C₉, hC₉, hC⟩ := wu_weighted_sq_le_envelope
  let D := 4 * C₉ * balancedAPEnvelopeConstant F * U
  have hD : 0 ≤ D := by dsimp [D]; positivity [balancedAPEnvelopeConstant_nonneg hF]
  refine ⟨Real.sqrt D + 1, by positivity, ?_⟩
  intro x Q S f r b hx hQ hS hf hr hUbound
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    norm_num at h
    exact h.le
  have hx2 : 2 ≤ x := htwo.trans hx
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  have hlog : 0 < Real.log x := by linarith
  have henv := balancedAPEnvelopeConstant_nonneg hF
  have hsq := hC x (balancedAPEnvelopeConstant F * x * (1 + Real.log x) ^ 2)
    Q (fun d => actualAPError S f r d (b d)) hx2 hQ (by positivity)
    (fun d _ => actualAPError_nonneg ..) (by
      intro d hd
      exact balanced_modulus_mul_actualAPError_le x F S f r d (b d) hx2 hF
        (mem_Icc.mp hd).1 ((by exact_mod_cast (mem_Icc.mp hd).2 : (d : ℝ) ≤ Q).trans hQ)
        hS hf hr)
  simp only [actualAPError_eq_abs_actualAPSum] at hsq
  have hmajor :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ^ 2 ≤
        D * (x / Real.log x ^ A) ^ 2 := by
    calc
      _ ≤ (C₉ * Real.log x ^ (9 : ℝ)) *
          ((balancedAPEnvelopeConstant F * x * (1 + Real.log x) ^ 2) *
              ∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) := hsq
      _ ≤ (C₉ * Real.log x ^ (9 : ℝ)) *
          ((balancedAPEnvelopeConstant F * x * (2 * Real.log x) ^ 2) *
              (U * x / Real.log x ^ (2 * A + 11))) := by
        gcongr
        linarith
      _ = _ := by
        dsimp [D]
        rw [Real.rpow_add hlog, mul_comm 2 A, Real.rpow_mul hlog.le]
        norm_cast
        field_simp [hlog.ne', (Real.rpow_pos_of_pos hlog A).ne']
        ring
  have hs :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ^ 2 ≤
        (Real.sqrt D * (x / Real.log x ^ A)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD]
    exact hmajor
  have hratio : 0 ≤ x / Real.log x ^ A := by positivity
  have hfinal := le_of_sq_le_sq hs (mul_nonneg (Real.sqrt_nonneg D) hratio)
  have hrelax : (Real.sqrt D + 1) * (x / Real.log x ^ A) =
      (Real.sqrt D + 1) * x / Real.log x ^ A := by ring
  rw [← hrelax]
  nlinarith

end
end Wu2004MeanValue