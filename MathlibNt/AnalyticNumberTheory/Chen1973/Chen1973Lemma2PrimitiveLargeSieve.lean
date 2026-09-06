/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveGaussFareyExactBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Chen 1973, Lemma 2: primitive-character large sieve

This is a source module for the lemma printed on pp. 113--114 of Chen's 1973
paper.  The definitions and theorem statements below retain the paper's exact
objects: the interval `M < n ≤ M + N`, primitive characters, the weights
`q / φ(q)` and `1 / φ(q)`, and the constant `X² + π N` in equation (2).

The proof on pp. 113--114 has two layers.  First, disjoint intervals around the
reduced Farey fractions give equation (4), the sharp additive estimate with
constant `X² + π N`.  Gauss inversion and character orthogonality then give
(2).  Finally the source partitions `D < q ≤ Q` into the cells
`2^i D < q ≤ 2^(i+1) D` and obtains (3).

The already-proved Gauss/Farey orthogonality layer is reused literally.  The
remaining source-calculus sentence (equation (4), whose sharp constant is not
provided by the repository's weaker logarithmic `largeSieveBound`) is exposed
as `Chen1973FareyEquationFour`; it is not replaced by the weaker bound.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Set MeasureTheory
open scoped BigOperators Interval

noncomputable section

/-- Chen p. 113: `S(α) = ∑_{n=M+1}^{M+N} a_n e(nα)`. -/
def chen1973ExponentialSum (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N),
    (a n : ℂ) * charReal ((n : ℝ) * α)

/-- Chen p. 113: `Z = ∑_{n=M+1}^{M+N} |a_n|²`. -/
def chen1973CoefficientEnergy (a : ℤ → ℝ) (M : ℤ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N), |a n| ^ 2

private def chen1973ShiftedExponentialSum (a : ℤ → ℝ) (M : ℤ) (N : ℕ)
    (τ α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N),
    (a n : ℂ) * charReal (((n : ℝ) - τ) * α)

private def chen1973ShiftedDerivativeSum (a : ℤ → ℝ) (M : ℤ) (N : ℕ)
    (τ α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N),
    (((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ)) *
      charReal (((n : ℝ) - τ) * α)

lemma charReal_intervalIntegral_int (k : ℤ) (u : ℝ) :
    (∫ x in u..u + 1, charReal ((k : ℝ) * x)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [charReal]
  · rw [if_neg hk]
    unfold charReal
    rw [show (fun x : ℝ => Complex.exp ((2 * Real.pi * (((k : ℝ) * x : ℝ) : ℂ)) * Complex.I)) =
        (fun x : ℝ => Complex.exp ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * x)) by
      funext x
      congr 1
      push_cast
      ring]
    rw [integral_exp_mul_complex]
    · have hkexp :
        Complex.exp ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * (u + 1)) =
          Complex.exp ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * u) := by
        rw [show ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * (u + 1)) =
            ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * u) +
              (k : ℂ) * (2 * Real.pi * Complex.I) by
              push_cast
              ring,
            Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]
      simp only [Complex.ofReal_add, Complex.ofReal_one]
      rw [hkexp, sub_self, zero_div]
    · have hkR : (k : ℝ) ≠ 0 := by
        exact_mod_cast hk
      exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hkR))
        Complex.I_ne_zero

lemma chen1973_fourier_parseval (s : Finset ℤ) (b : ℤ → ℂ) (u : ℝ) :
    (∫ x in u..u + 1, ‖∑ n ∈ s, b n * charReal ((n : ℝ) * x)‖ ^ 2) =
      ∑ n ∈ s, ‖b n‖ ^ 2 := by
  apply Complex.ofReal_inj.mp
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  rw [intervalIntegral.integral_congr (fun x _ =>
    normSq_sum_eq_sum_mul_star s (fun n => b n * charReal ((n : ℝ) * x)))]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    calc
      (∑ m ∈ s, ∫ x in u..u + 1,
          (b n * charReal ((n : ℝ) * x)) *
            star (b m * charReal ((m : ℝ) * x))) =
          ∑ m ∈ s, if n = m then ((‖b n‖ : ℂ) ^ 2) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [show (fun x : ℝ =>
            (b n * charReal ((n : ℝ) * x)) * star (b m * charReal ((m : ℝ) * x))) =
            (fun x : ℝ => (b n * star (b m)) *
              charReal (((n - m : ℤ) : ℝ) * x)) by
            funext x
            rw [star_mul]
            calc
              b n * charReal ((n : ℝ) * x) *
                  (star (charReal ((m : ℝ) * x)) * star (b m)) =
                (b n * star (b m)) *
                  (charReal ((n : ℝ) * x) * star (charReal ((m : ℝ) * x))) := by
                    ring
              _ = (b n * star (b m)) * charReal (((n - m : ℤ) : ℝ) * x) := by
                    rw [← charReal_sub]
                    congr 2
                    push_cast
                    ring]
        rw [intervalIntegral.integral_const_mul, charReal_intervalIntegral_int]
        by_cases hnm : n = m
        · subst m
          simp only [sub_self, if_pos, mul_one]
          calc
            b n * star (b n) = (Complex.normSq (b n) : ℂ) := Complex.mul_conj (b n)
            _ = (‖b n‖ : ℂ) ^ 2 := by
              rw [Complex.normSq_eq_norm_sq]
              norm_cast
        · have hsub : n - m ≠ 0 := sub_ne_zero.mpr hnm
          simp [hsub, hnm]
      _ = (‖b n‖ : ℂ) ^ 2 := by
        simp [hn]
    · intro m hm
      apply Continuous.intervalIntegrable
      unfold charReal
      fun_prop
  · intro n hn
    refine continuous_finsetSum _ ?_ |>.intervalIntegrable u (u + 1)
    intro m hm
    unfold charReal
    fun_prop

lemma chen1973_fourier_parseval_shift (s : Finset ℤ) (b : ℤ → ℂ) (τ u : ℝ) :
    (∫ x in u..u + 1, ‖∑ n ∈ s, b n * charReal (((n : ℝ) - τ) * x)‖ ^ 2) =
      ∑ n ∈ s, ‖b n‖ ^ 2 := by
  -- A frequency shift is multiplication by a unit-modulus character.
  have hmod (x : ℝ) :
      (∑ n ∈ s, b n * charReal (((n : ℝ) - τ) * x)) =
        charReal (-τ * x) * ∑ n ∈ s, b n * charReal ((n : ℝ) * x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show ((n : ℝ) - τ) * x = -τ * x + (n : ℝ) * x by ring, charReal_add]
    ring
  have hnorm (x : ℝ) : ‖charReal (-τ * x)‖ = 1 := by
    rw [charReal]
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi * (τ * x)))
  simp_rw [hmod, norm_mul, hnorm, one_mul]
  exact chen1973_fourier_parseval s b u

private lemma chen1973ShiftedExponentialSum_eq_modulation
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (τ α : ℝ) :
    chen1973ShiftedExponentialSum a M N τ α =
      (charReal (-τ * α) : ℂ) * chen1973ExponentialSum a M N α := by
  unfold chen1973ShiftedExponentialSum chen1973ExponentialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold charReal
  rw [show (2 * Real.pi * ((((n : ℝ) - τ) * α : ℝ) : ℂ)) * Complex.I =
      (2 * Real.pi * (((-τ * α : ℝ) : ℂ)) * Complex.I) +
        (2 * Real.pi * ((((n : ℝ) * α : ℝ) : ℂ)) * Complex.I) by
          push_cast
          ring,
      Complex.exp_add]
  ring

private lemma norm_chen1973ShiftedExponentialSum_eq
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (τ α : ℝ) :
    ‖chen1973ShiftedExponentialSum a M N τ α‖ =
      ‖chen1973ExponentialSum a M N α‖ := by
  rw [chen1973ShiftedExponentialSum_eq_modulation, norm_mul]
  have hnorm : ‖(charReal (-τ * α) : ℂ)‖ = 1 := by
    rw [charReal]
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi * (τ * α)))
  rw [hnorm, one_mul]

/- The derivative identity for the shifted exponential sum is the next local
source step in the proof of formula (4).  It is intentionally added only after
its direct Lean proof compiles; no unchecked draft is kept in this module. -/

private lemma hasDerivAt_charReal_mul (c x : ℝ) :
    HasDerivAt (fun y : ℝ => charReal (c * y))
      ((((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) * charReal (c * x)) x := by
  let K : ℂ := ((2 * Real.pi * c : ℝ) : ℂ) * Complex.I
  have hc : HasDerivAt (fun z : ℂ => Complex.exp (K * z))
      (Complex.exp (K * (x : ℂ)) * K) (x : ℂ) := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id (x : ℂ)).const_mul K).cexp
  simpa [charReal, K, mul_assoc, mul_left_comm, mul_comm] using hc.comp_ofReal

private lemma hasDerivAt_chen1973ShiftedExponentialSum
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (τ x : ℝ) :
    HasDerivAt (chen1973ShiftedExponentialSum a M N τ)
      (Complex.I * chen1973ShiftedDerivativeSum a M N τ x) x := by
  unfold chen1973ShiftedExponentialSum chen1973ShiftedDerivativeSum
  have h := HasDerivAt.sum (u := Finset.Icc (M + 1) (M + N)) (fun n hn =>
    (hasDerivAt_charReal_mul ((n : ℝ) - τ) x).const_mul (a n : ℂ))
  have hfun :
      (∑ i ∈ Finset.Icc (M + 1) (M + N), fun y => (a i : ℂ) * charReal (((i : ℝ) - τ) * y)) =
        (fun α => ∑ n ∈ Finset.Icc (M + 1) (M + N), (a n : ℂ) * charReal (((n : ℝ) - τ) * α)) := by
    funext α
    simp
  rw [hfun] at h
  have hd :
      Complex.I * ∑ n ∈ Finset.Icc (M + 1) (M + N),
          (((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ)) *
            charReal (((n : ℝ) - τ) * x) =
        ∑ n ∈ Finset.Icc (M + 1) (M + N),
          (a n : ℂ) *
            ((((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * Complex.I) *
              charReal (((n : ℝ) - τ) * x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hd]
  exact h

private lemma continuous_chen1973ShiftedExponentialSum
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (τ : ℝ) :
    Continuous (chen1973ShiftedExponentialSum a M N τ) := by
  unfold chen1973ShiftedExponentialSum
  refine continuous_finsetSum _ ?_
  intro n hn
  unfold charReal
  fun_prop

private lemma continuous_chen1973ShiftedDerivativeSum
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (τ : ℝ) :
    Continuous (chen1973ShiftedDerivativeSum a M N τ) := by
  unfold chen1973ShiftedDerivativeSum
  refine continuous_finsetSum _ ?_
  intro n hn
  unfold charReal
  fun_prop

private def chen1973Center (M : ℤ) (N : ℕ) : ℝ :=
  (M : ℝ) + ((N : ℝ) + 1) / 2

private lemma abs_sub_chen1973Center_le
    {M n : ℤ} {N : ℕ} (hn : n ∈ Finset.Icc (M + 1) (M + N)) :
    |(n : ℝ) - chen1973Center M N| ≤ (N : ℝ) / 2 := by
  rcases Finset.mem_Icc.mp hn with ⟨hnl, hnu⟩
  have hnlR : (M : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnl
  have hnuR : (n : ℝ) ≤ (M : ℝ) + N := by exact_mod_cast hnu
  dsimp [chen1973Center]
  rw [abs_le]
  constructor <;> linarith [hnlR, hnuR]

private lemma chen1973_shiftedDerivative_energy_le
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (u : ℝ) :
    (∫ x in u..u + 1,
        ‖chen1973ShiftedDerivativeSum a M N (chen1973Center M N) x‖ ^ 2) ≤
      (Real.pi * (N : ℝ)) ^ 2 * chen1973CoefficientEnergy a M N := by
  let τ : ℝ := chen1973Center M N
  let s : Finset ℤ := Finset.Icc (M + 1) (M + N)
  have hparse :
      (∫ x in u..u + 1, ‖chen1973ShiftedDerivativeSum a M N τ x‖ ^ 2) =
        ∑ n ∈ s, ‖(((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ))‖ ^ 2 := by
    simpa [chen1973ShiftedDerivativeSum, s, τ] using
    chen1973_fourier_parseval_shift s
      (fun n => (((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ))) τ u
  rw [hparse]
  have hsum :
      (∑ n ∈ s, ‖(((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ))‖ ^ 2) ≤
        ∑ n ∈ s, (Real.pi * (N : ℝ)) ^ 2 * ‖(a n : ℂ)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro n hn
    have hcenter : |(n : ℝ) - τ| ≤ (N : ℝ) / 2 := by
      simpa [τ, s] using abs_sub_chen1973Center_le (M := M) (N := N) hn
    have hcoef :
        ‖(((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ))‖ ≤
          Real.pi * (N : ℝ) * ‖(a n : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hfac : |2 * Real.pi * ((n : ℝ) - τ)| ≤ Real.pi * (N : ℝ) := by
        calc
          |2 * Real.pi * ((n : ℝ) - τ)| = (2 * Real.pi) * |(n : ℝ) - τ| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg Real.pi_pos.le]
          _ ≤ Real.pi * (N : ℝ) := by
            nlinarith [hcenter, Real.pi_pos]
      exact mul_le_mul_of_nonneg_right hfac (norm_nonneg ((a n : ℂ)))
    have hnonneg :
        0 ≤ Real.pi * (N : ℝ) * ‖(a n : ℂ)‖ := by positivity
    calc
      ‖(((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ))‖ ^ 2
          ≤ (Real.pi * (N : ℝ) * ‖(a n : ℂ)‖) ^ 2 := by
              nlinarith [hcoef, norm_nonneg ((((2 * Real.pi * ((n : ℝ) - τ) : ℝ) : ℂ) * (a n : ℂ))), hnonneg]
      _ = (Real.pi * (N : ℝ)) ^ 2 * ‖(a n : ℂ)‖ ^ 2 := by ring
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  gcongr
  simpa [s, chen1973CoefficientEnergy, Real.norm_eq_abs]

private lemma local_norm_sq_le_average_add_cross
    {f g : ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hf : Continuous f) (hg : Continuous g)
    (hderiv : ∀ x ∈ Set.Ioo u v, HasDerivAt f (Complex.I * g x) x) :
    ‖f u‖ ^ 2 ≤
      (v - u)⁻¹ * (∫ x in u..v, ‖f x‖ ^ 2) +
        ∫ x in u..v, (2 : ℝ) * ‖f x‖ * ‖g x‖ := by
  let F : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let B : ℝ → ℝ := fun x => (2 : ℝ) * ‖f x‖ * ‖g x‖
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  have hpoint : ∀ y ∈ Set.Icc u v, F u ≤ F y + ∫ x in u..v, B x := by
    intro y hy
    have huy : u ≤ y := hy.1
    have hyv : y ≤ v := hy.2
    have hFcontOn : ContinuousOn F (Set.Icc u y) := hFcont.continuousOn
    have hFdiffOn : DifferentiableOn ℝ F (Set.Ioo u y) := by
      intro t ht
      exact ((hderiv t ⟨ht.1, lt_of_lt_of_le ht.2 hyv⟩).norm_sq.differentiableAt).differentiableWithinAt
    have hBiuy : IntervalIntegrable B volume u y := hBcont.intervalIntegrable _ _
    have hBuv : IntervalIntegrable B volume u v := hBcont.intervalIntegrable _ _
    have hFB : ∀ᵐ t, t ∈ Set.Ioo u y → ‖deriv F t‖ ≤ B t := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have htuv : t ∈ Set.Ioo u v := ⟨ht.1, lt_of_lt_of_le ht.2 hyv⟩
      have hsq := (hderiv t htuv).norm_sq
      rw [show deriv F t = 2 * inner ℝ (f t) (Complex.I * g t) by
          dsimp [F]
          simpa using hsq.deriv]
      calc
        ‖(2 : ℝ) * inner ℝ (f t) (Complex.I * g t)‖ ≤
            ‖(2 : ℝ)‖ * (‖f t‖ * ‖Complex.I * g t‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
        _ = B t := by simp [B, mul_assoc]
    have hdisp :=
      norm_sub_le_integral_of_norm_deriv_le_of_le huy hFcontOn hFdiffOn hFB hBiuy
    have hmono :
        ∫ x in u..y, B x ≤ ∫ x in u..v, B x := by
      rw [intervalIntegral.integral_of_le huy, intervalIntegral.integral_of_le huv.le]
      apply MeasureTheory.integral_mono_measure
      · exact volume.restrict_mono_set (show Set.Ioc u y ⊆ Set.Ioc u v by
          intro t ht
          exact ⟨ht.1, ht.2.trans hyv⟩)
      · exact Filter.Eventually.of_forall fun t => by
          dsimp [B]
          positivity
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le).mp hBuv
    have hbase : F u ≤ F y + ∫ x in u..y, B x := by
      have habs : |F y - F u| ≤ ∫ x in u..y, B x := by
        simpa [Real.norm_eq_abs] using hdisp
      have hparts := abs_le.mp habs
      linarith
    linarith
  have hconst : IntervalIntegrable (fun _ : ℝ => F u) volume u v := intervalIntegrable_const
  have hsumInt : IntervalIntegrable (fun y : ℝ => F y + ∫ x in u..v, B x) volume u v := by
    exact (hFcont.intervalIntegrable _ _).add intervalIntegrable_const
  have hint :
      ∫ y in u..v, F u ≤ ∫ y in u..v, (F y + ∫ x in u..v, B x) := by
    apply intervalIntegral.integral_mono_on huv.le hconst hsumInt
    intro y hy
    exact hpoint y hy
  have hmain :
      (v - u) * F u ≤ (∫ y in u..v, F y) + (v - u) * ∫ x in u..v, B x := by
    calc
      (v - u) * F u = ∫ y in u..v, F u := by
        simp [intervalIntegral.integral_const]
      _ ≤ ∫ y in u..v, (F y + ∫ x in u..v, B x) := hint
      _ = (∫ y in u..v, F y) + (v - u) * ∫ x in u..v, B x := by
        rw [intervalIntegral.integral_add]
        · simp [intervalIntegral.integral_const]
        · exact hFcont.intervalIntegrable _ _
        · exact intervalIntegrable_const
  have hvu : 0 < v - u := sub_pos.mpr huv
  have hmul :
      (v - u) * ‖f u‖ ^ 2 ≤
        (v - u) *
          ((v - u)⁻¹ * (∫ x in u..v, ‖f x‖ ^ 2) +
            ∫ x in u..v, (2 : ℝ) * ‖f x‖ * ‖g x‖) := by
    calc
      (v - u) * ‖f u‖ ^ 2 = (v - u) * F u := by rfl
      _ ≤ (∫ y in u..v, F y) + (v - u) * ∫ x in u..v, B x := hmain
      _ = (v - u) *
            ((v - u)⁻¹ * (∫ x in u..v, ‖f x‖ ^ 2) +
              ∫ x in u..v, (2 : ℝ) * ‖f x‖ * ‖g x‖) := by
            dsimp [F, B]
            field_simp [hvu.ne']
  exact le_of_mul_le_mul_left hmul hvu

private lemma local_norm_sq_right_le_average_add_cross
    {f g : ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hf : Continuous f) (hg : Continuous g)
    (hderiv : ∀ x ∈ Set.Ioo u v, HasDerivAt f (Complex.I * g x) x) :
    ‖f v‖ ^ 2 ≤
      (v - u)⁻¹ * (∫ x in u..v, ‖f x‖ ^ 2) +
        ∫ x in u..v, (2 : ℝ) * ‖f x‖ * ‖g x‖ := by
  let F : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let B : ℝ → ℝ := fun x => (2 : ℝ) * ‖f x‖ * ‖g x‖
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  have hpoint : ∀ y ∈ Set.Icc u v, F v ≤ F y + ∫ x in u..v, B x := by
    intro y hy
    have huy : u ≤ y := hy.1
    have hyv : y ≤ v := hy.2
    have hFcontOn : ContinuousOn F (Set.Icc y v) := hFcont.continuousOn
    have hFdiffOn : DifferentiableOn ℝ F (Set.Ioo y v) := by
      intro t ht
      exact ((hderiv t ⟨lt_of_le_of_lt huy ht.1, ht.2⟩).norm_sq.differentiableAt).differentiableWithinAt
    have hByv : IntervalIntegrable B volume y v := hBcont.intervalIntegrable _ _
    have hBuv : IntervalIntegrable B volume u v := hBcont.intervalIntegrable _ _
    have hFB : ∀ᵐ t, t ∈ Set.Ioo y v → ‖deriv F t‖ ≤ B t := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have htuv : t ∈ Set.Ioo u v := ⟨lt_of_le_of_lt huy ht.1, ht.2⟩
      have hsq := (hderiv t htuv).norm_sq
      rw [show deriv F t = 2 * inner ℝ (f t) (Complex.I * g t) by
          dsimp [F]
          simpa using hsq.deriv]
      calc
        ‖(2 : ℝ) * inner ℝ (f t) (Complex.I * g t)‖ ≤
            ‖(2 : ℝ)‖ * (‖f t‖ * ‖Complex.I * g t‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
        _ = B t := by simp [B, mul_assoc]
    have hdisp :=
      norm_sub_le_integral_of_norm_deriv_le_of_le hyv hFcontOn hFdiffOn hFB hByv
    have hmono :
        ∫ x in y..v, B x ≤ ∫ x in u..v, B x := by
      rw [intervalIntegral.integral_of_le hyv, intervalIntegral.integral_of_le huv.le]
      apply MeasureTheory.integral_mono_measure
      · exact volume.restrict_mono_set (show Set.Ioc y v ⊆ Set.Ioc u v by
          intro t ht
          exact ⟨huy.trans_lt ht.1, ht.2⟩)
      · exact Filter.Eventually.of_forall fun t => by
          dsimp [B]
          positivity
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le).mp hBuv
    have hbase : F v ≤ F y + ∫ x in y..v, B x := by
      have habs : |F v - F y| ≤ ∫ x in y..v, B x := by
        simpa [Real.norm_eq_abs] using hdisp
      have hparts := abs_le.mp habs
      linarith
    linarith
  have hconst : IntervalIntegrable (fun _ : ℝ => F v) volume u v := intervalIntegrable_const
  have hsumInt : IntervalIntegrable (fun y : ℝ => F y + ∫ x in u..v, B x) volume u v := by
    exact (hFcont.intervalIntegrable _ _).add intervalIntegrable_const
  have hint :
      ∫ y in u..v, F v ≤ ∫ y in u..v, (F y + ∫ x in u..v, B x) := by
    apply intervalIntegral.integral_mono_on huv.le hconst hsumInt
    intro y hy
    exact hpoint y hy
  have hmain :
      (v - u) * F v ≤ (∫ y in u..v, F y) + (v - u) * ∫ x in u..v, B x := by
    calc
      (v - u) * F v = ∫ y in u..v, F v := by
        simp [intervalIntegral.integral_const]
      _ ≤ ∫ y in u..v, (F y + ∫ x in u..v, B x) := hint
      _ = (∫ y in u..v, F y) + (v - u) * ∫ x in u..v, B x := by
        rw [intervalIntegral.integral_add]
        · simp [intervalIntegral.integral_const]
        · exact hFcont.intervalIntegrable _ _
        · exact intervalIntegrable_const
  have hvu : 0 < v - u := sub_pos.mpr huv
  have hmul :
      (v - u) * ‖f v‖ ^ 2 ≤
        (v - u) *
          ((v - u)⁻¹ * (∫ x in u..v, ‖f x‖ ^ 2) +
            ∫ x in u..v, (2 : ℝ) * ‖f x‖ * ‖g x‖) := by
    calc
      (v - u) * ‖f v‖ ^ 2 = (v - u) * F v := by rfl
      _ ≤ (∫ y in u..v, F y) + (v - u) * ∫ x in u..v, B x := hmain
      _ = (v - u) *
            ((v - u)⁻¹ * (∫ x in u..v, ‖f x‖ ^ 2) +
              ∫ x in u..v, (2 : ℝ) * ‖f x‖ * ‖g x‖) := by
            dsimp [F, B]
            field_simp [hvu.ne']
  exact le_of_mul_le_mul_left hmul hvu

private lemma local_norm_sq_center_le_average_add_cross
    {f g : ℝ → ℂ} {c h : ℝ} (hh : 0 < h)
    (hf : Continuous f) (hg : Continuous g)
    (hderiv : ∀ x ∈ Set.Ioo (c - h) (c + h),
      HasDerivAt f (Complex.I * g x) x) :
    ‖f c‖ ^ 2 ≤
      (2 * h)⁻¹ * (∫ x in c - h..c + h, ‖f x‖ ^ 2) +
        ∫ x in c - h..c + h, ‖f x‖ * ‖g x‖ := by
  have hleft : c - h < c := by linarith
  have hright : c < c + h := by linarith
  have hL := local_norm_sq_right_le_average_add_cross hleft hf hg
    (fun x hx => hderiv x ⟨hx.1, hx.2.trans hright⟩)
  have hR := local_norm_sq_le_average_add_cross hright hf hg
    (fun x hx => hderiv x ⟨hleft.trans hx.1, hx.2⟩)
  have hsqL : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume (c - h) c := by
    exact (hf.norm.pow 2).intervalIntegrable _ _
  have hsqR : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume c (c + h) := by
    exact (hf.norm.pow 2).intervalIntegrable _ _
  have hcrossL : IntervalIntegrable (fun x => ‖f x‖ * ‖g x‖) volume (c - h) c := by
    exact (hf.norm.mul hg.norm).intervalIntegrable _ _
  have hcrossR : IntervalIntegrable (fun x => ‖f x‖ * ‖g x‖) volume c (c + h) := by
    exact (hf.norm.mul hg.norm).intervalIntegrable _ _
  have htwoL :
      (∫ x in c - h..c, (2 : ℝ) * ‖f x‖ * ‖g x‖) =
        2 * ∫ x in c - h..c, ‖f x‖ * ‖g x‖ := by
    rw [show (fun x => (2 : ℝ) * ‖f x‖ * ‖g x‖) =
        (fun x => (2 : ℝ) * (‖f x‖ * ‖g x‖)) by funext x; ring,
      intervalIntegral.integral_const_mul]
  have htwoR :
      (∫ x in c..c + h, (2 : ℝ) * ‖f x‖ * ‖g x‖) =
        2 * ∫ x in c..c + h, ‖f x‖ * ‖g x‖ := by
    rw [show (fun x => (2 : ℝ) * ‖f x‖ * ‖g x‖) =
        (fun x => (2 : ℝ) * (‖f x‖ * ‖g x‖)) by funext x; ring,
      intervalIntegral.integral_const_mul]
  calc
    ‖f c‖ ^ 2 ≤
        (1 / 2 : ℝ) *
          ((h⁻¹ * (∫ x in c - h..c, ‖f x‖ ^ 2) +
              (∫ x in c - h..c, (2 : ℝ) * ‖f x‖ * ‖g x‖)) +
            (h⁻¹ * (∫ x in c..c + h, ‖f x‖ ^ 2) +
              (∫ x in c..c + h, (2 : ℝ) * ‖f x‖ * ‖g x‖))) := by
          have hsubL : (c - (c - h))⁻¹ = h⁻¹ := by congr 1 <;> ring
          have hsubR : (c + h - c)⁻¹ = h⁻¹ := by congr 1 <;> ring
          rw [hsubL] at hL
          rw [hsubR] at hR
          nlinarith
    _ = (2 * h)⁻¹ *
          ((∫ x in c - h..c, ‖f x‖ ^ 2) +
            ∫ x in c..c + h, ‖f x‖ ^ 2) +
        ((∫ x in c - h..c, ‖f x‖ * ‖g x‖) +
          ∫ x in c..c + h, ‖f x‖ * ‖g x‖) := by
            rw [htwoL, htwoR]
            field_simp [hh.ne']
            ring
    _ = (2 * h)⁻¹ * (∫ x in c - h..c + h, ‖f x‖ ^ 2) +
        ∫ x in c - h..c + h, ‖f x‖ * ‖g x‖ := by
          rw [intervalIntegral.integral_add_adjacent_intervals hsqL hsqR,
            intervalIntegral.integral_add_adjacent_intervals hcrossL hcrossR]

private def chen1973FareyRadius (X : ℕ) : ℝ :=
  1 / (2 * (X : ℝ) ^ 2)

private def chen1973FareyArc (X : ℕ) (qa : ℕ × ℕ) : Set ℝ :=
  Set.Ioc (reducedFareyPoint qa - chen1973FareyRadius X)
    (reducedFareyPoint qa + chen1973FareyRadius X)

private lemma two_mul_chen1973FareyRadius {X : ℕ} (hX : 0 < X) :
    2 * chen1973FareyRadius X = 1 / (X : ℝ) ^ 2 := by
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  simp only [chen1973FareyRadius]
  field_simp

private lemma reducedFareyPoint_bounds_for_arc {X : ℕ} (hX : 0 < X)
    {qa : ℕ × ℕ} (hqa : qa ∈ reducedFareyIndices X) :
    0 ≤ reducedFareyPoint qa ∧
      reducedFareyPoint qa ≤ 1 - 1 / (X : ℝ) ^ 2 := by
  rcases qa with ⟨q, r⟩
  rw [mem_reducedFareyIndices] at hqa
  rw [reducedFareyPoint_pair]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqa.1
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hrq : (r : ℝ) ≤ (q : ℝ) - 1 := by
    have hrqNat : r + 1 ≤ q := by omega
    have hrqR : (r : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hrqNat
    linarith
  have hqXsq : (q : ℝ) ≤ (X : ℝ) ^ 2 := by
    have hqX : q ≤ X := hqa.2.1
    have hXX : X ≤ X ^ 2 := by nlinarith
    exact_mod_cast hqX.trans hXX
  constructor
  · positivity
  · rw [div_le_iff₀ hqR]
    have hdiv : (q : ℝ) / (X : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (sq_pos_of_pos hXR)]
      exact hqXsq
    calc
      (r : ℝ) ≤ (q : ℝ) - 1 := hrq
      _ ≤ (1 - 1 / (X : ℝ) ^ 2) * (q : ℝ) := by
        rw [sub_mul, one_mul, div_mul_eq_mul_div]
        ring_nf at hdiv ⊢
        linarith

private lemma distToInt_le_abs_of_abs_lt_one {z : ℝ} (hz : |z| < 1) :
    distToInt z ≤ |z| := by
  by_cases hz0 : 0 ≤ z
  · have hz1 : z < 1 := by simpa [abs_of_nonneg hz0] using hz
    have hfract : Int.fract z = z := Int.fract_eq_self.mpr ⟨hz0, hz1⟩
    rw [distToInt, hfract, abs_of_nonneg hz0]
    exact min_le_left _ _
  · have hzneg : z < 0 := lt_of_not_ge hz0
    have hzm1 : (-1 : ℝ) < z := by
      rw [abs_of_neg hzneg] at hz
      linarith
    have hfloor : ⌊z⌋ = (-1 : ℤ) :=
      Int.floor_eq_on_Ico (-1) z ⟨by simpa using hzm1.le, by simpa using hzneg⟩
    rw [distToInt, Int.fract, hfloor, abs_of_neg hzneg]
    norm_num

private lemma chen1973FareyArc_disjoint {X : ℕ} (hX : 0 < X)
    {qa qb : ℕ × ℕ} (hqa : qa ∈ reducedFareyIndices X)
    (hqb : qb ∈ reducedFareyIndices X) (hne : qa ≠ qb) :
    Disjoint (chen1973FareyArc X qa) (chen1973FareyArc X qb) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  rw [chen1973FareyArc, Set.mem_Ioc] at hxa hxb
  let p := reducedFareyPoint qa
  let q := reducedFareyPoint qb
  let h := chen1973FareyRadius X
  have hp := reducedFareyPoint_bounds_for_arc hX hqa
  have hq := reducedFareyPoint_bounds_for_arc hX hqb
  have hδpos : 0 < 1 / (X : ℝ) ^ 2 := by positivity
  have htwo : 2 * h = 1 / (X : ℝ) ^ 2 := by
    simpa [h] using two_mul_chen1973FareyRadius hX
  have hpq_ne : p ≠ q := by
    intro hpq
    apply hne
    exact reducedFareyPoint_injOn X hqa hqb hpq
  have hp_mem : p ∈ reducedFareyPoints X := by
    exact Finset.mem_image.mpr ⟨qa, hqa, rfl⟩
  have hq_mem : q ∈ reducedFareyPoints X := by
    exact Finset.mem_image.mpr ⟨qb, hqb, rfl⟩
  have hspace : 1 / (X : ℝ) ^ 2 ≤ distToInt (p - q) :=
    reducedFareyPoints_wellSpaced X hX hp_mem hq_mem hpq_ne
  have habslt : |p - q| < 1 := by
    rw [abs_lt]
    constructor <;> dsimp [p, q] at * <;> linarith [hδpos]
  have hsep : 1 / (X : ℝ) ^ 2 ≤ |p - q| :=
    hspace.trans (distToInt_le_abs_of_abs_lt_one habslt)
  have hoverlap : |p - q| < 2 * h := by
    rw [abs_lt]
    constructor
    · dsimp [p, q, h] at hxa hxb ⊢
      linarith
    · dsimp [p, q, h] at hxa hxb ⊢
      linarith
  rw [htwo] at hoverlap
  exact (not_lt_of_ge hsep) hoverlap

private lemma chen1973FareyArcs_pairwiseDisjoint {X : ℕ} (hX : 0 < X) :
    Set.Pairwise (↑(reducedFareyIndices X) : Set (ℕ × ℕ))
      (fun qa qb => Disjoint (chen1973FareyArc X qa) (chen1973FareyArc X qb)) := by
  intro qa hqa qb hqb hne
  exact chen1973FareyArc_disjoint hX hqa hqb hne

private lemma chen1973FareyArc_subset_unitInterval {X : ℕ} (hX : 0 < X)
    {qa : ℕ × ℕ} (hqa : qa ∈ reducedFareyIndices X) :
    chen1973FareyArc X qa ⊆
      Set.Ioc (-chen1973FareyRadius X) (1 - chen1973FareyRadius X) := by
  intro x hx
  rw [chen1973FareyArc, Set.mem_Ioc] at hx
  rw [Set.mem_Ioc]
  have hp := reducedFareyPoint_bounds_for_arc hX hqa
  have htwo := two_mul_chen1973FareyRadius hX
  constructor
  · linarith
  · linarith

private lemma sum_fareyArc_integrals_le_unitInterval
    {X : ℕ} (hX : 0 < X) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) :
    (∑ qa ∈ reducedFareyIndices X,
        ∫ x in reducedFareyPoint qa - chen1973FareyRadius X..
          reducedFareyPoint qa + chen1973FareyRadius X, φ x) ≤
      ∫ x in -chen1973FareyRadius X..1 - chen1973FareyRadius X, φ x := by
  let s := reducedFareyIndices X
  let A : ℕ × ℕ → Set ℝ := fun qa => chen1973FareyArc X qa
  let U : Set ℝ := ⋃ qa ∈ s, A qa
  let J : Set ℝ := Set.Ioc (-chen1973FareyRadius X) (1 - chen1973FareyRadius X)
  have hh : 0 < chen1973FareyRadius X := by
    dsimp [chen1973FareyRadius]
    positivity
  have hA_meas : ∀ qa ∈ s, MeasurableSet (A qa) := by
    intro qa hqa
    exact measurableSet_Ioc
  have hA_int : ∀ qa ∈ s, IntegrableOn φ (A qa) volume := by
    intro qa hqa
    dsimp [A, chen1973FareyArc]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith :
      reducedFareyPoint qa - chen1973FareyRadius X ≤
        reducedFareyPoint qa + chen1973FareyRadius X)]
    exact hφ.intervalIntegrable _ _
  have hpair : Set.Pairwise (↑s : Set (ℕ × ℕ))
      (fun qa qb => Disjoint (A qa) (A qb)) := by
    simpa [s, A] using chen1973FareyArcs_pairwiseDisjoint hX
  have hUJ : U ⊆ J := by
    intro x hx
    change x ∈ ⋃ qa ∈ s, A qa at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨qa, hqa, hxA⟩ := hx
    exact chen1973FareyArc_subset_unitInterval hX hqa hxA
  have hJ_int : IntegrableOn φ J volume := by
    dsimp [J]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith :
      -chen1973FareyRadius X ≤ 1 - chen1973FareyRadius X)]
    exact hφ.intervalIntegrable _ _
  calc
    (∑ qa ∈ reducedFareyIndices X,
        ∫ x in reducedFareyPoint qa - chen1973FareyRadius X..
          reducedFareyPoint qa + chen1973FareyRadius X, φ x) =
        ∑ qa ∈ s, ∫ x in A qa, φ x := by
          apply Finset.sum_congr rfl
          intro qa hqa
          rw [intervalIntegral.integral_of_le (by linarith :
            reducedFareyPoint qa - chen1973FareyRadius X ≤
              reducedFareyPoint qa + chen1973FareyRadius X)]
          rfl
    _ = ∫ x in U, φ x := by
          exact (MeasureTheory.integral_biUnion_finset s hA_meas hpair hA_int).symm
    _ ≤ ∫ x in J, φ x := by
          exact MeasureTheory.setIntegral_mono_set hJ_int
            (Filter.Eventually.of_forall hφ_nonneg)
            (Filter.Eventually.of_forall fun x =>
              show x ∈ U → x ∈ J from fun hx => hUJ hx)
    _ = ∫ x in -chen1973FareyRadius X..1 - chen1973FareyRadius X, φ x := by
          rw [intervalIntegral.integral_of_le (by linarith :
            -chen1973FareyRadius X ≤ 1 - chen1973FareyRadius X)]

private lemma chen1973_shifted_energy_eq
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) (u : ℝ) :
    (∫ x in u..u + 1,
        ‖chen1973ShiftedExponentialSum a M N (chen1973Center M N) x‖ ^ 2) =
      chen1973CoefficientEnergy a M N := by
  simpa [chen1973ShiftedExponentialSum, chen1973CoefficientEnergy,
    Real.norm_eq_abs] using
    chen1973_fourier_parseval_shift (Finset.Icc (M + 1) (M + N))
      (fun n => (a n : ℂ)) (chen1973Center M N) u

private lemma chen1973_cross_integral_le
    (a : ℤ → ℝ) (M : ℤ) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    (∫ x in u..u + 1,
        ‖chen1973ShiftedExponentialSum a M N (chen1973Center M N) x‖ *
          ‖chen1973ShiftedDerivativeSum a M N (chen1973Center M N) x‖) ≤
      Real.pi * (N : ℝ) * chen1973CoefficientEnergy a M N := by
  let F := chen1973ShiftedExponentialSum a M N (chen1973Center M N)
  let G := chen1973ShiftedDerivativeSum a M N (chen1973Center M N)
  let P : ℝ := Real.pi * (N : ℝ)
  let E : ℝ := chen1973CoefficientEnergy a M N
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hFcont : Continuous F := continuous_chen1973ShiftedExponentialSum _ _ _ _
  have hGcont : Continuous G := continuous_chen1973ShiftedDerivativeSum _ _ _ _
  have hpoint : ∀ x : ℝ,
      ‖F x‖ * ‖G x‖ ≤
        (P / 2) * ‖F x‖ ^ 2 + (1 / (2 * P)) * ‖G x‖ ^ 2 := by
    intro x
    calc
      ‖F x‖ * ‖G x‖ ≤
          (P ^ 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2) / (2 * P) := by
        rw [le_div_iff₀ (by positivity : 0 < 2 * P)]
        nlinarith [sq_nonneg (P * ‖F x‖ - ‖G x‖)]
      _ = (P / 2) * ‖F x‖ ^ 2 + (1 / (2 * P)) * ‖G x‖ ^ 2 := by
        field_simp [hP.ne']
  have hmono :
      (∫ x in u..u + 1, ‖F x‖ * ‖G x‖) ≤
        ∫ x in u..u + 1,
          ((P / 2) * ‖F x‖ ^ 2 + (1 / (2 * P)) * ‖G x‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (hFcont.norm.mul hGcont.norm).intervalIntegrable _ _
    · exact ((hFcont.norm.pow 2).const_mul _ |>.add
        ((hGcont.norm.pow 2).const_mul _)).intervalIntegrable _ _
    · intro x hx
      exact hpoint x
  have hF2 : (∫ x in u..u + 1, ‖F x‖ ^ 2) = E := by
    simpa [F, E] using chen1973_shifted_energy_eq a M N u
  have hG2 : (∫ x in u..u + 1, ‖G x‖ ^ 2) ≤ P ^ 2 * E := by
    simpa [G, P, E] using chen1973_shiftedDerivative_energy_le a M N u
  calc
    (∫ x in u..u + 1, ‖F x‖ * ‖G x‖) ≤
        ∫ x in u..u + 1,
          ((P / 2) * ‖F x‖ ^ 2 + (1 / (2 * P)) * ‖G x‖ ^ 2) := hmono
    _ = (P / 2) * (∫ x in u..u + 1, ‖F x‖ ^ 2) +
          (1 / (2 * P)) * (∫ x in u..u + 1, ‖G x‖ ^ 2) := by
        rw [intervalIntegral.integral_add]
        · rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
        · exact (hFcont.norm.pow 2).const_mul _ |>.intervalIntegrable _ _
        · exact (hGcont.norm.pow 2).const_mul _ |>.intervalIntegrable _ _
    _ ≤ (P / 2) * E + (1 / (2 * P)) * (P ^ 2 * E) := by
        rw [hF2]
        gcongr
    _ = P * E := by
        field_simp [hP.ne']
        ring

/-- The character amplitude occurring verbatim in equations (2) and (3). -/
def chen1973PrimitiveAmplitude (a : ℤ → ℝ) (M : ℤ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N),
    (a n : ℂ) * χ.1 (n : ZMod q)

/-- Chen pp. 113--114, equation (4): the sharp reduced-Farey additive estimate.
This is exactly the analytic sentence between the disjoint-interval argument
and primitive Gauss inversion. -/
def Chen1973FareyEquationFour : Prop :=
  ∀ (a : ℤ → ℝ) (M : ℤ) (N X : ℕ),
    (∑ qa ∈ reducedFareyIndices X,
        ‖chen1973ExponentialSum a M N (reducedFareyPoint qa)‖ ^ 2) ≤
      ((X : ℝ) ^ 2 + Real.pi * (N : ℝ)) *
        chen1973CoefficientEnergy a M N

/-- Unconditional closure of Chen's sharp Farey estimate, equation (4). -/
theorem chen1973FareyEquationFour : Chen1973FareyEquationFour := by
  intro a M N X
  by_cases hX0 : X = 0
  · subst X
    simp [reducedFareyIndices, chen1973CoefficientEnergy]
    exact mul_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun n hn => sq_nonneg _)
  by_cases hN0 : N = 0
  · subst N
    simp [chen1973ExponentialSum, chen1973CoefficientEnergy]
  have hX : 0 < X := Nat.pos_of_ne_zero hX0
  have hN : 0 < N := Nat.pos_of_ne_zero hN0
  let h := chen1973FareyRadius X
  let τ := chen1973Center M N
  let F := chen1973ShiftedExponentialSum a M N τ
  let G := chen1973ShiftedDerivativeSum a M N τ
  let E := chen1973CoefficientEnergy a M N
  have hh : 0 < h := by
    dsimp [h, chen1973FareyRadius]
    positivity
  have htwo : 2 * h = 1 / (X : ℝ) ^ 2 := by
    simpa [h] using two_mul_chen1973FareyRadius hX
  have hinv : (2 * h)⁻¹ = (X : ℝ) ^ 2 := by
    rw [htwo]
    have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
    field_simp
  have hFcont : Continuous F := by
    simpa [F, τ] using continuous_chen1973ShiftedExponentialSum a M N τ
  have hGcont : Continuous G := by
    simpa [G, τ] using continuous_chen1973ShiftedDerivativeSum a M N τ
  have hlocal : ∀ qa ∈ reducedFareyIndices X,
      ‖chen1973ExponentialSum a M N (reducedFareyPoint qa)‖ ^ 2 ≤
        (X : ℝ) ^ 2 *
          (∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
            ‖F x‖ ^ 2) +
        ∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
          ‖F x‖ * ‖G x‖ := by
    intro qa hqa
    have hc := local_norm_sq_center_le_average_add_cross hh hFcont hGcont
      (fun x hx => by
        simpa [F, G, τ] using
          hasDerivAt_chen1973ShiftedExponentialSum a M N τ x)
      (c := reducedFareyPoint qa)
    rw [hinv] at hc
    simpa [F, G, τ, norm_chen1973ShiftedExponentialSum_eq, h] using hc
  have hsum := Finset.sum_le_sum hlocal
  have hFpay :
      (∑ qa ∈ reducedFareyIndices X,
          ∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
            ‖F x‖ ^ 2) ≤ E := by
    calc
      _ ≤ ∫ x in -h..1 - h, ‖F x‖ ^ 2 := by
        simpa [h] using sum_fareyArc_integrals_le_unitInterval hX
          (fun x => ‖F x‖ ^ 2) (hFcont.norm.pow 2) (fun x => sq_nonneg _)
      _ = E := by
        convert chen1973_shifted_energy_eq a M N (-h) using 1 <;>
          simp [F, τ, E] <;> ring
  have hCpay :
      (∑ qa ∈ reducedFareyIndices X,
          ∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
            ‖F x‖ * ‖G x‖) ≤ Real.pi * (N : ℝ) * E := by
    calc
      _ ≤ ∫ x in -h..1 - h, ‖F x‖ * ‖G x‖ := by
        simpa [h] using sum_fareyArc_integrals_le_unitInterval hX
          (fun x => ‖F x‖ * ‖G x‖) (hFcont.norm.mul hGcont.norm)
          (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ Real.pi * (N : ℝ) * E := by
        convert chen1973_cross_integral_le a M hN (-h) using 1 <;>
          simp [F, G, τ, E] <;> ring
  calc
    (∑ qa ∈ reducedFareyIndices X,
        ‖chen1973ExponentialSum a M N (reducedFareyPoint qa)‖ ^ 2) ≤
      ∑ qa ∈ reducedFareyIndices X,
        ((X : ℝ) ^ 2 *
          (∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
            ‖F x‖ ^ 2) +
        ∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
          ‖F x‖ * ‖G x‖) := hsum
    _ = (X : ℝ) ^ 2 *
          (∑ qa ∈ reducedFareyIndices X,
            ∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
              ‖F x‖ ^ 2) +
        (∑ qa ∈ reducedFareyIndices X,
          ∫ x in reducedFareyPoint qa - h..reducedFareyPoint qa + h,
            ‖F x‖ * ‖G x‖) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (X : ℝ) ^ 2 * E + Real.pi * (N : ℝ) * E := by
      gcongr
    _ = ((X : ℝ) ^ 2 + Real.pi * (N : ℝ)) *
        chen1973CoefficientEnergy a M N := by
      dsimp [E]
      ring

/-- Chen p. 113, equation (2), as one literal proposition. -/
def Chen1973Lemma2EquationTwo : Prop :=
  ∀ (a : ℤ → ℝ) (M : ℤ) (N X : ℕ),
    (∑ q ∈ Finset.Icc 1 X,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖chen1973PrimitiveAmplitude a M N q χ‖ ^ 2) ≤
      ((X : ℝ) ^ 2 + Real.pi * (N : ℝ)) *
        chen1973CoefficientEnergy a M N

/-- Chen p. 113, equation (3), with the Vinogradov constant made explicit and
its source dependence preserved: one absolute constant works uniformly for
`a, M, N, D, Q`. -/
def Chen1973Lemma2EquationThree : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (a : ℤ → ℝ) (M : ℤ) (N D Q : ℕ), 0 < D →
      (∑ q ∈ Finset.Ioc D Q,
          (1 / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖chen1973PrimitiveAmplitude a M N q χ‖ ^ 2) ≤
        C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          chen1973CoefficientEnergy a M N

@[simp]
theorem chen1973PrimitiveAmplitude_eq_intervalAmplitude
    (a : ℤ → ℝ) (M : ℤ) (N q : ℕ) (χ : PrimitiveCharacter q) :
    chen1973PrimitiveAmplitude a M N q χ =
      primitiveIntervalAmplitude (fun n => (a n : ℂ)) M N χ := by
  rfl

@[simp]
theorem chen1973CoefficientEnergy_eq_norm_energy
    (a : ℤ → ℝ) (M : ℤ) (N : ℕ) :
    chen1973CoefficientEnergy a M N =
      ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖(a n : ℂ)‖ ^ 2 := by
  unfold chen1973CoefficientEnergy
  apply Finset.sum_congr rfl
  intro n hn
  simp [Real.norm_eq_abs]

@[simp]
theorem chen1973ExponentialSum_eq_reducedAdditiveAmplitude
    (a : ℤ → ℝ) (M : ℤ) (N q r : ℕ) :
    chen1973ExponentialSum a M N ((r : ℝ) / (q : ℝ)) =
      reducedAdditiveAmplitude q (fun n => (a n : ℂ)) M N r := by
  unfold chen1973ExponentialSum reducedAdditiveAmplitude
  apply Finset.sum_congr rfl
  intro n hn
  ring_nf

/-- Source sentence after (4), pp. 113--114: Gauss inversion plus primitive
character orthogonality turns the sharp reduced-Farey estimate into (2).
The final conclusion is the literal equation-(2) proposition. -/
theorem chen1973Lemma2_equationTwo_of_fareyEquationFour
    (h4 : Chen1973FareyEquationFour) : Chen1973Lemma2EquationTwo := by
  intro a M N X
  by_cases hX : X = 0
  · subst X
    simp [chen1973CoefficientEnergy]
    positivity
  · have hXpos : 0 < X := Nat.pos_of_ne_zero hX
    calc
      (∑ q ∈ Finset.Icc 1 X,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖chen1973PrimitiveAmplitude a M N q χ‖ ^ 2) ≤
        ∑ qa ∈ reducedFareyIndices X,
          ‖chen1973ExponentialSum a M N (reducedFareyPoint qa)‖ ^ 2 := by
            calc
              _ ≤ ∑ q ∈ Finset.Icc 1 X, ∑ r ∈ reducedResidues q,
                  ‖reducedAdditiveAmplitude q (fun n => (a n : ℂ)) M N r‖ ^ 2 := by
                    apply Finset.sum_le_sum
                    intro q hq
                    letI : NeZero q :=
                      ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
                    simpa using
                      (weightedPrimitiveSquareLedger_le_reducedAdditive_of_directBessel
                        (primitiveReducedBesselDirect q)
                        (fun n => (a n : ℂ)) M N)
              _ = ∑ qa ∈ reducedFareyIndices X,
                  ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
                    (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) *
                      (a n : ℂ)‖ ^ 2 :=
                    reducedAdditiveEnergy_reindex_exact
                      (fun n => (a n : ℂ)) M N X
              _ = _ := by
                    apply Finset.sum_congr rfl
                    intro qa hqa
                    congr 2
                    rw [chen1973ExponentialSum]
                    apply Finset.sum_congr rfl
                    intro n hn
                    ring
      _ ≤ ((X : ℝ) ^ 2 + Real.pi * (N : ℝ)) *
          chen1973CoefficientEnergy a M N := h4 a M N X

/-! ## The dyadic modulus decomposition used for equation (3) -/

/-- The source cell `2^k D < q ≤ 2^(k+1)D`, intersected with `(D,Q]`. -/
def chen1973ModulusCell (D Q k : ℕ) : Finset ℕ :=
  (Finset.Ioc D Q).filter fun q =>
    Nat.log2 ((q - 1) / D) = k

@[simp]
theorem mem_chen1973ModulusCell {D Q k q : ℕ} :
    q ∈ chen1973ModulusCell D Q k ↔
      D < q ∧ q ≤ Q ∧ Nat.log2 ((q - 1) / D) = k := by
  simp [chen1973ModulusCell, and_assoc]

/-- A modulus in the `k`th cell lies in the literal source interval
`2^k D < q ≤ 2^(k+1)D`. -/
theorem chen1973ModulusCell_bounds {D Q k q : ℕ} (hD : 0 < D)
    (hq : q ∈ chen1973ModulusCell D Q k) :
    2 ^ k * D < q ∧ q ≤ 2 ^ (k + 1) * D := by
  rw [mem_chen1973ModulusCell] at hq
  let r := (q - 1) / D
  have hqpos : 0 < q := hD.trans hq.1
  have hqsub : D ≤ q - 1 := by omega
  have hrpos : 0 < r := by
    dsimp [r]
    exact Nat.div_pos hqsub hD
  have hk : Nat.log2 r = k := hq.2.2
  have hlo : 2 ^ k ≤ r := by
    rw [← hk]
    exact Nat.log2_self_le (Nat.ne_of_gt hrpos)
  have hrmul : r * D ≤ q - 1 := by
    dsimp [r]
    exact Nat.div_mul_le_self (q - 1) D
  have hlower : 2 ^ k * D ≤ q - 1 :=
    (Nat.mul_le_mul_right D hlo).trans hrmul
  have hrlt : r < 2 ^ (k + 1) := by
    rw [← hk]
    exact Nat.lt_log2_self
  have hdivlt : q - 1 < (r + 1) * D := by
    dsimp [r]
    exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hD
  have hupper : q ≤ 2 ^ (k + 1) * D := by
    have hrsucc : r + 1 ≤ 2 ^ (k + 1) := by omega
    have := (Nat.mul_le_mul_right D hrsucc)
    omega
  exact ⟨by omega, hupper⟩

/-- The chosen cell index is bounded by the last cell meeting `(D,Q]`. -/
theorem chen1973ModulusCell_index_lt {D Q k q : ℕ} (hD : 0 < D)
    (hq : q ∈ chen1973ModulusCell D Q k) :
    k < Nat.log2 ((Q - 1) / D) + 1 := by
  rw [mem_chen1973ModulusCell] at hq
  have hqsub : q - 1 ≤ Q - 1 := by omega
  have hdiv : (q - 1) / D ≤ (Q - 1) / D := Nat.div_le_div_right hqsub
  have hrpos : 0 < (q - 1) / D := by
    exact Nat.div_pos (by omega) hD
  have hlog : Nat.log2 ((q - 1) / D) ≤ Nat.log2 ((Q - 1) / D) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hdiv
  omega

/-- The dyadic cells partition the complete source interval `(D,Q]`. -/
theorem sum_chen1973ModulusCell
    {R : Type*} [AddCommMonoid R] (D Q : ℕ) (hD : 0 < D) (f : ℕ → R) :
    (∑ k ∈ Finset.range (Nat.log2 ((Q - 1) / D) + 1),
        ∑ q ∈ chen1973ModulusCell D Q k, f q) =
      ∑ q ∈ Finset.Ioc D Q, f q := by
  -- Swap the finite sums: each modulus contributes at its unique cell index.
  simp_rw [chen1973ModulusCell, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hown : q ∈ chen1973ModulusCell D Q (Nat.log2 ((q - 1) / D)) := by
    simp [chen1973ModulusCell, hq]
  have hidx := chen1973ModulusCell_index_lt hD hown
  simp only [Finset.sum_ite_eq, Finset.mem_range, if_pos hidx]

/-- One source dyadic cell, obtained from (2) at cutoff `2^(k+1)D` and the
pointwise inequality `1/q ≤ 1/(2^k D)`. -/
theorem chen1973EquationThree_cell_le
    (h2 : Chen1973Lemma2EquationTwo) (a : ℤ → ℝ) (M : ℤ)
    (N D Q k : ℕ) (hD : 0 < D) :
    (∑ q ∈ chen1973ModulusCell D Q k,
        (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖chen1973PrimitiveAmplitude a M N q χ‖ ^ 2) ≤
      (4 * ((2 ^ k * D : ℕ) : ℝ) +
          Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ)) *
        chen1973CoefficientEnergy a M N := by
  let A : ℕ := 2 ^ k * D
  let B : ℕ := 2 ^ (k + 1) * D
  let E : ℕ → ℝ := fun q =>
    ∑ χ : PrimitiveCharacter q,
      ‖chen1973PrimitiveAmplitude a M N q χ‖ ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hsubset : chen1973ModulusCell D Q k ⊆ Finset.Icc 1 B := by
    intro q hq
    have hb := chen1973ModulusCell_bounds hD hq
    exact Finset.mem_Icc.mpr ⟨by omega, by simpa [B] using hb.2⟩
  have hpoint : ∀ q ∈ chen1973ModulusCell D Q k,
      (1 / (q.totient : ℝ)) * E q ≤
        (1 / (A : ℝ)) * (((q : ℝ) / (q.totient : ℝ)) * E q) := by
    intro q hq
    have hqA := (chen1973ModulusCell_bounds hD hq).1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hA.trans hqA
    have hφpos : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hE : 0 ≤ E q := Finset.sum_nonneg fun χ hχ => sq_nonneg _
    rw [show (1 / (q.totient : ℝ)) * E q =
      (1 / (q : ℝ)) * (((q : ℝ) / (q.totient : ℝ)) * E q) by
        field_simp]
    have hAr : (0 : ℝ) < A := by exact_mod_cast hA
    have hAq : (A : ℝ) ≤ q := by exact_mod_cast hqA.le
    exact mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le hAr hAq)
      (mul_nonneg (div_nonneg hqpos.le hφpos.le) hE)
  calc
    (∑ q ∈ chen1973ModulusCell D Q k,
        (1 / (q.totient : ℝ)) * E q) ≤
      ∑ q ∈ chen1973ModulusCell D Q k,
        (1 / (A : ℝ)) * (((q : ℝ) / (q.totient : ℝ)) * E q) :=
          Finset.sum_le_sum hpoint
    _ = (1 / (A : ℝ)) *
        ∑ q ∈ chen1973ModulusCell D Q k,
          ((q : ℝ) / (q.totient : ℝ)) * E q := by rw [Finset.mul_sum]
    _ ≤ (1 / (A : ℝ)) *
        ∑ q ∈ Finset.Icc 1 B,
          ((q : ℝ) / (q.totient : ℝ)) * E q := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro q hq hnot
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun χ hχ => sq_nonneg _)
      · positivity
    _ ≤ (1 / (A : ℝ)) *
        (((B : ℝ) ^ 2 + Real.pi * (N : ℝ)) *
          chen1973CoefficientEnergy a M N) := by
      apply mul_le_mul_of_nonneg_left (h2 a M N B)
      positivity
    _ = (4 * ((2 ^ k * D : ℕ) : ℝ) +
          Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ)) *
        chen1973CoefficientEnergy a M N := by
      dsimp [A, B]
      have hden : ((2 ^ k * D : ℕ) : ℝ) ≠ 0 := by positivity
      rw [show ((2 ^ (k + 1) * D : ℕ) : ℝ) =
        2 * ((2 ^ k * D : ℕ) : ℝ) by
          norm_cast
          rw [pow_succ]
          ring]
      field_simp
      ring

/-- Finite geometric identity used in Chen's dyadic summation. -/
theorem sum_range_two_pow (K : ℕ) :
    (∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ K - 1 := by
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using
    geom_sum_eq (show (2 : ℝ) ≠ 1 by norm_num) K

/-- The reciprocal dyadic tail has total mass at most two. -/
theorem sum_range_inv_two_pow_le_two (K : ℕ) :
    (∑ k ∈ Finset.range K, (1 / (2 : ℝ)) ^ k) ≤ 2 := by
  have hid : (∑ k ∈ Finset.range K, (1 / (2 : ℝ)) ^ k) +
      2 * (1 / (2 : ℝ)) ^ K = 2 := by
    induction K with
    | zero => norm_num
    | succ K ih =>
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith
  have hnonneg : 0 ≤ 2 * (1 / (2 : ℝ)) ^ K := by positivity
  linarith

/-- The exact geometric payment in the proof of (3).  The two source sums are
bounded respectively by `8Q` and `2πN/D`. -/
theorem chen1973_dyadic_scalar_sum_le (N D Q : ℕ) (hD : 0 < D) (hDQ : D < Q) :
    let K := Nat.log2 ((Q - 1) / D) + 1
    (∑ k ∈ Finset.range K,
      (4 * ((2 ^ k * D : ℕ) : ℝ) +
        Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ))) ≤
      8 * (Q : ℝ) + 2 * Real.pi * (N : ℝ) / (D : ℝ) := by
  dsimp only
  let K := Nat.log2 ((Q - 1) / D) + 1
  let r := (Q - 1) / D
  have hr : 0 < r := by
    dsimp [r]
    exact Nat.div_pos (by omega) hD
  have hlo : 2 ^ Nat.log2 r ≤ r := Nat.log2_self_le (Nat.ne_of_gt hr)
  have hrmul : r * D ≤ Q - 1 := by
    dsimp [r]
    exact Nat.div_mul_le_self (Q - 1) D
  have hpNat : 2 ^ K * D ≤ 2 * Q := by
    have hbase : 2 ^ Nat.log2 r * D ≤ Q - 1 :=
      (Nat.mul_le_mul_right D hlo).trans hrmul
    calc
      2 ^ K * D = 2 * (2 ^ Nat.log2 r * D) := by
        dsimp [K]
        rw [pow_succ]
        ring
      _ ≤ 2 * (Q - 1) := Nat.mul_le_mul_left 2 hbase
      _ ≤ 2 * Q := by omega
  have hp : (((2 : ℝ) ^ K) * (D : ℝ)) ≤ 2 * (Q : ℝ) := by
    exact_mod_cast hpNat
  have hfirst :
      (∑ k ∈ Finset.range K, 4 * ((2 ^ k * D : ℕ) : ℝ)) ≤
        8 * (Q : ℝ) := by
    calc
      _ = 4 * (D : ℝ) *
          (∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            ring
      _ = 4 * (D : ℝ) * ((2 : ℝ) ^ K - 1) := by
            rw [sum_range_two_pow]
      _ ≤ 4 * (D : ℝ) * (2 : ℝ) ^ K := by
            have hDr : (0 : ℝ) ≤ D := by positivity
            nlinarith
      _ ≤ 8 * (Q : ℝ) := by nlinarith
  have hsecond :
      (∑ k ∈ Finset.range K,
        Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ)) ≤
        2 * Real.pi * (N : ℝ) / (D : ℝ) := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    calc
      _ = (Real.pi * (N : ℝ) / (D : ℝ)) *
          ∑ k ∈ Finset.range K, (1 / (2 : ℝ)) ^ k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            rw [one_div, inv_pow]
            field_simp
      _ ≤ (Real.pi * (N : ℝ) / (D : ℝ)) * 2 := by
            apply mul_le_mul_of_nonneg_left (sum_range_inv_two_pow_le_two K)
            positivity
      _ = _ := by ring
  rw [Finset.sum_add_distrib]
  exact add_le_add hfirst hsecond

/-- Chen p. 114: summing the dyadic cells proves equation (3).  We exhibit the
absolute constant `8 + 2π`; the printed `≪` only records existence of such a
constant and has no dependence on `a, M, N, D`, or `Q`. -/
theorem chen1973Lemma2_equationThree_of_equationTwo
    (h2 : Chen1973Lemma2EquationTwo) : Chen1973Lemma2EquationThree := by
  refine ⟨8 + 2 * Real.pi, by positivity, ?_⟩
  intro a M N D Q hD
  by_cases hDQ : D < Q
  · let K := Nat.log2 ((Q - 1) / D) + 1
    let E : ℕ → ℝ := fun q =>
      ∑ χ : PrimitiveCharacter q,
        ‖chen1973PrimitiveAmplitude a M N q χ‖ ^ 2
    have henergy : 0 ≤ chen1973CoefficientEnergy a M N := by
      unfold chen1973CoefficientEnergy
      positivity
    rw [← sum_chen1973ModulusCell D Q hD
      (fun q => (1 / (q.totient : ℝ)) * E q)]
    calc
      (∑ k ∈ Finset.range K,
          ∑ q ∈ chen1973ModulusCell D Q k,
            (1 / (q.totient : ℝ)) * E q) ≤
        ∑ k ∈ Finset.range K,
          (4 * ((2 ^ k * D : ℕ) : ℝ) +
            Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ)) *
              chen1973CoefficientEnergy a M N := by
        apply Finset.sum_le_sum
        intro k hk
        exact chen1973EquationThree_cell_le h2 a M N D Q k hD
      _ = (∑ k ∈ Finset.range K,
          (4 * ((2 ^ k * D : ℕ) : ℝ) +
            Real.pi * (N : ℝ) / ((2 ^ k * D : ℕ) : ℝ))) *
              chen1973CoefficientEnergy a M N := by
        rw [Finset.sum_mul]
      _ ≤ (8 * (Q : ℝ) + 2 * Real.pi * (N : ℝ) / (D : ℝ)) *
          chen1973CoefficientEnergy a M N := by
        apply mul_le_mul_of_nonneg_right _ henergy
        exact chen1973_dyadic_scalar_sum_le N D Q hD hDQ
      _ ≤ (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          chen1973CoefficientEnergy a M N := by
        apply mul_le_mul_of_nonneg_right _ henergy
        have hid :
            (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) =
              (8 * (Q : ℝ) + 2 * Real.pi * (N : ℝ) / (D : ℝ)) +
                (2 * Real.pi * (Q : ℝ) + 8 * ((N : ℝ) / (D : ℝ))) := by ring
        rw [hid]
        exact le_add_of_nonneg_right (add_nonneg (by positivity) (by positivity))
  · have hQD : Q ≤ D := Nat.le_of_not_gt hDQ
    have hempty : Finset.Ioc D Q = ∅ := by
      ext q
      simp
      omega
    rw [hempty]
    simp
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)

/-- Chen's complete Lemma 2 reduction: the sharp Farey equation (4) gives the
literal primitive equation (2), and its dyadic summation gives (3). -/
theorem chen1973Lemma2_of_fareyEquationFour
    (h4 : Chen1973FareyEquationFour) :
    Chen1973Lemma2EquationTwo ∧ Chen1973Lemma2EquationThree := by
  have h2 := chen1973Lemma2_equationTwo_of_fareyEquationFour h4
  exact ⟨h2, chen1973Lemma2_equationThree_of_equationTwo h2⟩

end

end AnalyticNumberTheory.LargeSieve
