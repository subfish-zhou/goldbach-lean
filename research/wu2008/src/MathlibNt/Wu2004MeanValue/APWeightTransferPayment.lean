import MathlibNt.Wu2004MeanValue.APWeightTransfer

/-!
# Reciprocal ninth-moment payment at the actual AP level

Only the explicitly named unweighted actual AP mass is an input to the
last theorem. The arbitrary-coefficient envelope and the divisor moment
are proved inputs, not extra analytic hypotheses.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.Richert1969

noncomputable section

/-- One fixed divisor-moment constant works for every nonnegative error
sequence with the stated elementary modulus envelope. -/
theorem wu_weighted_sq_le_envelope :
    ∃ C₉ : ℝ, 0 < C₉ ∧ ∀ (x X : ℝ) (Q : ℕ) (E : ℕ → ℝ),
      2 ≤ x → (Q : ℝ) ≤ x → 0 ≤ X →
      (∀ d ∈ Icc 1 Q, 0 ≤ E d) →
      (∀ d ∈ Icc 1 Q, (d : ℝ) * E d ≤ X) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * E d) ^ 2 ≤
        (C₉ * Real.log x ^ (9 : ℝ)) * (X * ∑ d ∈ Icc 1 Q, E d) := by
  obtain ⟨J, hJ, hmoment⟩ := lemma3NineOmegaMass_le_polylog
  refine ⟨J * 2 ^ (9 : ℝ), by positivity, ?_⟩
  intro x X Q E hx hQ hX hE henv
  let T := (Icc 1 Q).filter Squarefree
  have hT : ∀ d ∈ T, d ∈ Icc 1 Q := fun d hd => (mem_filter.mp hd).1
  have hc := weightedError_sq_le_lemma3Mass_mul_ordinary T
    (fun d => (3 : ℝ) ^ d.primeFactors.card) E X
    (fun d hd => (mem_Icc.mp (hT d hd)).1)
    (fun d hd => hE d (hT d hd)) (fun d hd => henv d (hT d hd))
  have heq : (∑ d ∈ T, ((3 : ℝ) ^ d.primeFactors.card) ^ 2 / d) =
      lemma3NineOmegaMass T := by
    unfold lemma3NineOmegaMass
    apply sum_congr rfl
    intro d _
    rw [pow_two, ← mul_pow]
    norm_num
  rw [heq] at hc
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogQ : Real.log (Q + 2 : ℝ) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x * x) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul (by linarith) (by linarith)]; ring
  have hm : lemma3NineOmegaMass T ≤
      (J * 2 ^ (9 : ℝ)) * Real.log x ^ (9 : ℝ) := by
    calc
      _ ≤ J * Real.log (Q + 2) ^ (9 : ℝ) := hmoment Q T
        (fun d hd => mem_range.mpr (by have := (mem_Icc.mp (hT d hd)).2; omega))
        (fun d hd => (mem_filter.mp hd).2)
      _ ≤ J * (2 * Real.log x) ^ (9 : ℝ) := by
        gcongr
        exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) Q; linarith)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hlog.le]; ring
  rw [wu_weighted_sum_eq_squarefree]
  calc
    threeOmegaErrorMass T E ^ 2 ≤
        lemma3NineOmegaMass T * (X * ∑ d ∈ T, E d) := hc
    _ ≤ ((J * 2 ^ (9 : ℝ)) * Real.log x ^ (9 : ℝ)) *
        (X * ∑ d ∈ T, E d) :=
      mul_le_mul_of_nonneg_right hm
        (mul_nonneg hX (sum_nonneg (fun d hd => hE d (hT d hd))))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hX
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun d hd _ => hE d hd)

/-- Actual arbitrary bounded coefficients and one common profile, with the
residue selected by the modulus but never by the source coordinate. -/
theorem actualAP_weighted_sq_le_unweighted :
    ∃ C₉ : ℝ, 0 < C₉ ∧ ∀ (x F K : ℝ) (Q : ℕ)
      (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      2 ≤ x → 0 ≤ F → 0 ≤ K → (Q : ℝ) ≤ Real.sqrt x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * actualAPError S f r d (b d)) ^ 2 ≤
        (C₉ * Real.log x ^ (9 : ℝ)) *
          (((apEnvelopeConstant F K * richertReciprocalTotientConstant) *
            x * (1 + Real.log x) ^ 2) *
              ∑ d ∈ Icc 1 Q, actualAPError S f r d (b d)) := by
  obtain ⟨C₉, hC₉, hC⟩ := wu_weighted_sq_le_envelope
  refine ⟨C₉, hC₉, ?_⟩
  intro x F K Q S f r b hx hF hK hQ hS hf hr
  apply hC x _ Q _ hx
    (hQ.trans (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))))
    (by positivity [apEnvelopeConstant_nonneg hF hK,
      richertReciprocalTotientConstant_pos])
    (fun d _ => actualAPError_nonneg ..)
  intro d hd
  exact modulus_mul_actualAPError_le x F K S f r d (b d) hx hF hK
    (mem_Icc.mp hd).1
    ((by exact_mod_cast (mem_Icc.mp hd).2 : (d : ℝ) ≤ Q).trans hQ) hS hf hr

/-- Explicit arbitrary-saving transfer. An unweighted saving `2*A+11`
pays Wu's exact `mu² 3^omega` weight. The constant is selected before the
scale, cutoff, common coefficient/profile and modulus-selected residue.
The only estimate assumed is the genuine unweighted actual AP sum. -/
theorem actualAP_weighted_log_saving_of_unweighted (A F K U : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hU : 0 ≤ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (Q : ℕ)
      (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      Real.exp 1 ≤ x → (Q : ℝ) ≤ Real.sqrt x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      (∑ d ∈ Icc 1 Q, actualAPError S f r d (b d)) ≤
        U * x / Real.log x ^ (2 * A + 11) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * actualAPError S f r d (b d)) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨C₉, hC₉, hC⟩ := actualAP_weighted_sq_le_unweighted
  let D := 4 * C₉ * apEnvelopeConstant F K * richertReciprocalTotientConstant * U
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity [apEnvelopeConstant_nonneg hF hK, richertReciprocalTotientConstant_pos]
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
  have henv : 0 ≤ apEnvelopeConstant F K * richertReciprocalTotientConstant :=
    mul_nonneg (apEnvelopeConstant_nonneg hF hK) richertReciprocalTotientConstant_pos.le
  have hmajor :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * actualAPError S f r d (b d)) ^ 2 ≤
        D * (x / Real.log x ^ A) ^ 2 := by
    calc
      _ ≤ (C₉ * Real.log x ^ (9 : ℝ)) *
          (((apEnvelopeConstant F K * richertReciprocalTotientConstant) *
            x * (1 + Real.log x) ^ 2) *
              ∑ d ∈ Icc 1 Q, actualAPError S f r d (b d)) :=
        hC x F K Q S f r b hx2 hF hK hQ hS hf hr
      _ ≤ (C₉ * Real.log x ^ (9 : ℝ)) *
          (((apEnvelopeConstant F K * richertReciprocalTotientConstant) *
            x * (2 * Real.log x) ^ 2) *
              (U * x / Real.log x ^ (2 * A + 11))) := by
        gcongr
        · exact sum_nonneg (fun d _ => actualAPError_nonneg ..)
        · linarith
      _ = _ := by
        dsimp [D]
        rw [Real.rpow_add hlog, mul_comm 2 A, Real.rpow_mul hlog.le]
        norm_cast
        field_simp [hlog.ne', (Real.rpow_pos_of_pos hlog A).ne']
        ring
  have hs :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * actualAPError S f r d (b d)) ^ 2 ≤
        (Real.sqrt D * (x / Real.log x ^ A)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD]
    exact hmajor
  have hratio : 0 ≤ x / Real.log x ^ A := by positivity
  have hfinal := le_of_sq_le_sq hs
    (mul_nonneg (Real.sqrt_nonneg D) hratio)
  have hrelax : (Real.sqrt D + 1) * (x / Real.log x ^ A) =
      (Real.sqrt D + 1) * x / Real.log x ^ A := by ring
  rw [← hrelax]
  nlinarith

end
end Wu2004MeanValue