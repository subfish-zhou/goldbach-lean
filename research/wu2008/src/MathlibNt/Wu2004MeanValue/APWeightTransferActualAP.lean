import MathlibNt.Wu2004MeanValue.APWeightTransferPayment
import MathlibNt.Wu2004MeanValue.ActualAP

namespace Wu2004MeanValue

open Finset
open scoped BigOperators
open MathlibNt.SieveTheory.Richert1969

noncomputable section

theorem actualAPError_eq_abs_actualAPSum (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ) :
    actualAPError S f r d b = |actualAPSum S f r d b| := by
  classical
  simp only [actualAPError, actualAPSum, sum_filter]

/-- The weight transfer consumes exactly the parent's actual unweighted
AP source sum, with its common coefficient/profile and selected residue. -/
theorem actualAPSum_weighted_log_saving_of_unweighted (A F K U : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hU : 0 ≤ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (Q : ℕ)
      (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      Real.exp 1 ≤ x → (Q : ℝ) ≤ Real.sqrt x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      (∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) ≤
        U * x / Real.log x ^ (2 * A + 11) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ≤
        C * x / Real.log x ^ A := by
  simpa only [actualAPError_eq_abs_actualAPSum] using
    actualAP_weighted_log_saving_of_unweighted A F K U hF hK hU

/-- Finite interpolation with the full logarithmic loss displayed. The
carrier `S` may be just the large-source mask; no small-source mass occurs. -/
theorem actualAPSum_weighted_sq_le_log_eleven :
    ∃ C₉ : ℝ, 0 < C₉ ∧ ∀ (x F K : ℝ) (Q : ℕ)
      (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      Real.exp 1 ≤ x → 0 ≤ F → 0 ≤ K → (Q : ℝ) ≤ Real.sqrt x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ^ 2 ≤
        (4 * C₉ * apEnvelopeConstant F K * richertReciprocalTotientConstant) *
          x * Real.log x ^ (11 : ℝ) *
            (∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) := by
  obtain ⟨C₉, hC₉, hC⟩ := actualAP_weighted_sq_le_unweighted
  refine ⟨C₉, hC₉, ?_⟩
  intro x F K Q S f r b hx hF hK hQ hS hf hr
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    norm_num at h
    exact h.le
  have hx2 : 2 ≤ x := htwo.trans hx
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  have henv := mul_nonneg (apEnvelopeConstant_nonneg hF hK)
    richertReciprocalTotientConstant_pos.le
  have h := hC x F K Q S f r b hx2 hF hK hQ hS hf hr
  simp only [actualAPError_eq_abs_actualAPSum] at h
  calc
    _ ≤ (C₉ * Real.log x ^ (9 : ℝ)) *
        (((apEnvelopeConstant F K * richertReciprocalTotientConstant) *
          x * (1 + Real.log x) ^ 2) *
            ∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) := h
    _ ≤ (C₉ * Real.log x ^ (9 : ℝ)) *
        (((apEnvelopeConstant F K * richertReciprocalTotientConstant) *
          x * (2 * Real.log x) ^ 2) *
            ∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) := by
      gcongr
      linarith
    _ = _ := by
      norm_cast
      ring

/-- A large-source unweighted saving `T` pays any weighted saving `A`
with `T ≥ 2*A+11`. In particular the parent may choose `T=2*A+12`
before selecting its conductor split, source cutoff and final modulus level. -/
theorem actualAPSum_weighted_log_saving_of_unweighted_exponent
    (A T F K U : ℝ) (hT : 2 * A + 11 ≤ T)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hU : 0 ≤ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (Q : ℕ)
      (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      Real.exp 1 ≤ x → (Q : ℝ) ≤ Real.sqrt x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      (∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) ≤
        U * x / Real.log x ^ T →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨C, hC, htransfer⟩ :=
    actualAPSum_weighted_log_saving_of_unweighted A F K U hF hK hU
  refine ⟨C, hC, ?_⟩
  intro x Q S f r b hx hQ hS hf hr hmass
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  apply htransfer x Q S f r b hx hQ hS hf hr
  exact hmass.trans (div_le_div_of_nonneg_left (mul_nonneg hU hx0.le)
    (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hlog1 hT))

end
end Wu2004MeanValue