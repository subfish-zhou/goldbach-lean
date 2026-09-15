import MathlibNt.Wu2004MeanValue.APWeightTransfer
import MathlibNt.Wu2004MeanValue.ActualOpenIntervals

/-!
# Aggregate payment of actual open-upper-endpoint atoms

The count at an open upper endpoint loses at most one prime per positive
source index. Summing this literal loss in Wu's modulus weight is harmless
at a sufficiently logarithmically reduced square-root level.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators

noncomputable section

theorem wu_weight_sum_le_totient_mass (Q : ℕ) :
    (∑ d ∈ Icc 1 Q, wuModulusWeight d) ≤
      (Q : ℝ) * (∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d) := by
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hphi : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hd0
  have hphiQ : (Nat.totient d : ℝ) ≤ Q := by
    exact_mod_cast (Nat.totient_le d).trans (mem_Icc.mp hd).2
  calc
    _ = (Nat.totient d : ℝ) * (wuModulusWeight d / Nat.totient d) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hphiQ
      (div_nonneg (wuModulusWeight_nonneg d) hphi.le)

theorem weighted_upperEndpoint_sum_le (x F : ℝ) (Q : ℕ) (S : Finset ℕ)
    (f : ℕ → ℝ) (hi : ℕ → ℕ → ℝ) (b : ℕ → ℕ)
    (hF : 0 ≤ F)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x)
    (hf : ∀ m ∈ S, |f m| ≤ F) :
    (∑ d ∈ Icc 1 Q, wuModulusWeight d *
      |∑ m ∈ S.filter (fun m => m.Coprime d),
        f m * (upperEndpointSet (hi d m) d (b d) m).card|) ≤
      F * Real.sqrt x * Q *
        (∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d) := by
  have hpoint (d : ℕ) :
      |∑ m ∈ S.filter (fun m => m.Coprime d),
        f m * (upperEndpointSet (hi d m) d (b d) m).card| ≤ F * Real.sqrt x := by
    let T := S.filter (fun m => m.Coprime d)
    exact (abs_sum_upperEndpoint_le T (hi d) f d (b d) F hF
      (fun m hm => (hS m (mem_filter.mp hm).1).1)
      (fun m hm => hf m (mem_filter.mp hm).1)).trans
      (mul_le_mul_of_nonneg_left
        (small_support_card_le T _ (Real.sqrt_nonneg x)
          (fun m hm => hS m (mem_filter.mp hm).1)) hF)
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d * (F * Real.sqrt x) := by
      exact sum_le_sum (fun d _ =>
        mul_le_mul_of_nonneg_left (hpoint d) (wuModulusWeight_nonneg d))
    _ = (F * Real.sqrt x) * (∑ d ∈ Icc 1 Q, wuModulusWeight d) := by
      rw [← sum_mul]
      ring
    _ ≤ (F * Real.sqrt x) *
        ((Q : ℝ) * (∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d)) :=
      mul_le_mul_of_nonneg_left (wu_weight_sum_le_totient_mass Q) (by positivity)
    _ = _ := by ring

/-- Full aggregate payment of the literal endpoint atoms. Endpoints may
even be chosen separately for every modulus and source coordinate. The
cutoff exponent `A+6` is explicit; there is no analytic error assumption. -/
theorem weighted_upperEndpoint_log_saving (A F : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (Q : ℕ) (S : Finset ℕ)
      (f : ℕ → ℝ) (hi : ℕ → ℕ → ℝ) (b : ℕ → ℕ),
      Real.exp 1 ≤ x →
      (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ (A + 6) →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |∑ m ∈ S.filter (fun m => m.Coprime d),
          f m * (upperEndpointSet (hi d m) d (b d) m).card|) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨J, hJ, hmass⟩ := wu_reciprocal_totient_sum_bound
  refine ⟨F * J + 1, by positivity, ?_⟩
  intro x Q S f hi b hx hQ hS hf
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    norm_num at h
    exact h.le
  have hx2 : 2 ≤ x := htwo.trans hx
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  have hlog : 0 < Real.log x := by linarith
  have hQroot : (Q : ℝ) ≤ Real.sqrt x :=
    hQ.trans (div_le_self (Real.sqrt_nonneg x)
      (Real.one_le_rpow hlog1 (by linarith)))
  have hQx : (Q : ℝ) ≤ x :=
    hQroot.trans (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith)))
  calc
    _ ≤ F * Real.sqrt x * Q *
        (∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d) :=
      weighted_upperEndpoint_sum_le x F Q S f hi b hF hS hf
    _ ≤ F * Real.sqrt x * (Real.sqrt x / Real.log x ^ (A + 6)) *
        (J * Real.log x ^ (6 : ℝ)) := by
      gcongr
      · exact sum_nonneg (fun d _ =>
          div_nonneg (wuModulusWeight_nonneg d) (by positivity))
      · exact hmass x hx2 Q hQx
    _ = (F * J) * x / Real.log x ^ A := by
      rw [Real.rpow_add hlog]
      field_simp
      nlinarith [Real.sq_sqrt hx0.le]
    _ ≤ _ := by gcongr; linarith

/-- Direct aggregate payment for the atom in `actualOpenErrorSum_eq`. -/
theorem actualEndpointSum_weighted_log_saving (A F : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (Q : ℕ) (S : Finset ℕ)
      (f : ℕ → ℝ) (hi : ℕ → ℕ → ℝ) (b : ℕ → ℕ),
      Real.exp 1 ≤ x →
      (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ (A + 6) →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualEndpointSum S f (hi d) d (b d)|) ≤
        C * x / Real.log x ^ A := by
  simpa only [actualEndpointSum] using weighted_upperEndpoint_log_saving A F hA hF

end
end Wu2004MeanValue
