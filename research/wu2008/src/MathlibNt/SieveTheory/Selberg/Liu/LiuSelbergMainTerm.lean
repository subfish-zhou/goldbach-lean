import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergRemainder
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainSum
import Mathlib.NumberTheory.SelbergSieve

/-!
# Liu's factored Selberg main term

This module separates the exact finite factorization of Liu's `M₁` from the two
analytic estimates needed to bound its factors.  The component bounds below are
transparent propositions; no Selberg or logarithmic-integral estimate is
asserted.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset

noncomputable def liuSelbergReciprocalTotient : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else 1 / Nat.totient d
  map_zero' := by simp

lemma liuSelbergReciprocalTotient_isMultiplicative :
    liuSelbergReciprocalTotient.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [liuSelbergReciprocalTotient]
  · intro m n hm hn hmn
    simp [liuSelbergReciprocalTotient, hm, hn, Nat.totient_mul hmn, mul_comm]

/-- The quadratic Selberg coefficient factor on Liu's finite source carrier. -/
noncomputable def liuSelbergCoefficientFactor
    (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
    ∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
      lambda d1 * lambda d2 / Nat.totient (Nat.lcm d1 d2)

lemma prime_dvd_liuPaperQModulus
    {N p : ℕ} {epsilon : ℝ} (hp : p.Prime) :
    p ∣ liuPaperQModulus N epsilon ↔
      p ≤ paperQSourceCutoff N epsilon ∧ ¬p ∣ N := by
  rw [liuPaperQModulus_eq_paperQStyleModulus]
  exact prime_dvd_paperQStyleModulus hp

noncomputable def liuSelbergBoundingSieve
    (N : ℕ) (epsilon : ℝ) (hNeven : Even N) : BoundingSieve where
  support := ∅
  prodPrimes := liuPaperQModulus N epsilon
  prodPrimes_squarefree := liuPaperQModulus_squarefree N epsilon
  weights := fun _ => 0
  weights_nonneg := by intro n; simp
  totalMass := 0
  nu := liuSelbergReciprocalTotient
  nu_mult := liuSelbergReciprocalTotient_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hpQ
    have hphi : 0 < (Nat.totient p : ℝ) := by
      exact_mod_cast (Nat.totient_pos.mpr hp.pos)
    simpa [liuSelbergReciprocalTotient, hp.ne_zero, one_div] using (inv_pos.2 hphi)
  nu_lt_one_of_prime := by
    intro p hp hpQ
    have hpN : ¬p ∣ N := (prime_dvd_liuPaperQModulus (N := N) (epsilon := epsilon) hp).mp hpQ |>.2
    have hp_ne_two : p ≠ 2 := by
      intro hp_two
      exact hpN (hp_two.symm ▸ hNeven.two_dvd)
    have hp_gt_two : 2 < p := by
      exact lt_of_le_of_ne hp.two_le (by simpa using hp_ne_two.symm)
    have hphi_nat : 1 < Nat.totient p := by
      rw [Nat.totient_prime hp]
      omega
    have hphi : 1 < (Nat.totient p : ℝ) := by
      exact_mod_cast hphi_nat
    have hphi_pos : 0 < (Nat.totient p : ℝ) := by
      linarith
    simpa [liuSelbergReciprocalTotient, hp.ne_zero, one_div] using
      (inv_lt_one₀ hphi_pos).2 hphi

/-- Expanding the source carrier back to all divisors of the source modulus loses
only terms whose lambda coefficient vanishes off the source support. -/
theorem fullDivisors_quadraticSum_eq_liuSelbergCoefficientFactor_of_support
    {N : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hlambda : ∀ d, lambda d ≠ 0 →
      d ∣ liuPaperQModulus N epsilon ∧ d ≤ paperQSourceCutoff N epsilon) :
    (liuPaperQModulus N epsilon).divisors.sum (fun d1 =>
      (liuPaperQModulus N epsilon).divisors.sum (fun d2 =>
        lambda d1 * lambda d2 / Nat.totient (Nat.lcm d1 d2))) =
      liuSelbergCoefficientFactor N epsilon lambda := by
  classical
  unfold liuSelbergCoefficientFactor liuSelbergLambdaSourceCarrier
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d1 hd1
  by_cases h1 : d1 ≤ paperQSourceCutoff N epsilon
  · simp only [h1, if_true]
    apply Finset.sum_congr rfl
    intro d2 hd2
    by_cases h2 : d2 ≤ paperQSourceCutoff N epsilon
    · simp [h2]
    · have hzero : lambda d2 = 0 := by
        by_contra hne
        exact h2 ((hlambda d2 hne).2)
      simp [h2, hzero]
  · have hzero : lambda d1 = 0 := by
      by_contra hne
      exact h1 ((hlambda d1 hne).2)
    simp [h1, hzero]

/-- The coefficient/diagonal-main-sum identity needs only source support, not
the separate absolute bound used by Liu's remainder estimate. -/
theorem liuSelbergCoefficientFactor_eq_mainSum_lambdaSquared_of_support
    {N : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hNeven : Even N)
    (hlambda : ∀ d, lambda d ≠ 0 →
      d ∣ liuPaperQModulus N epsilon ∧ d ≤ paperQSourceCutoff N epsilon) :
    (liuSelbergBoundingSieve N epsilon hNeven).mainSum
        (BoundingSieve.lambdaSquared lambda) =
      liuSelbergCoefficientFactor N epsilon lambda := by
  let S := liuSelbergBoundingSieve N epsilon hNeven
  have hQpos : 0 < liuPaperQModulus N epsilon :=
    Nat.pos_of_ne_zero (liuPaperQModulus_squarefree N epsilon).ne_zero
  calc
    S.mainSum (BoundingSieve.lambdaSquared lambda) =
        ∑ d1 ∈ (liuPaperQModulus N epsilon).divisors,
          ∑ d2 ∈ (liuPaperQModulus N epsilon).divisors,
            S.nu d1 * lambda d1 * S.nu d2 * lambda d2 *
              (S.nu (d1.gcd d2))⁻¹ := by
      simpa [S, liuSelbergBoundingSieve] using
        (BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul (s := S) lambda)
    _ =
        ∑ d1 ∈ (liuPaperQModulus N epsilon).divisors,
          ∑ d2 ∈ (liuPaperQModulus N epsilon).divisors,
            lambda d1 * lambda d2 / Nat.totient (Nat.lcm d1 d2) := by
      apply Finset.sum_congr rfl
      intro d1 hd1
      apply Finset.sum_congr rfl
      intro d2 hd2
      have hd1dvd : d1 ∣ liuPaperQModulus N epsilon := (Nat.mem_divisors.mp hd1).1
      have hd2dvd : d2 ∣ liuPaperQModulus N epsilon := (Nat.mem_divisors.mp hd2).1
      have hd1pos : 0 < d1 := Nat.pos_of_dvd_of_pos hd1dvd hQpos
      have hd2pos : 0 < d2 := Nat.pos_of_dvd_of_pos hd2dvd hQpos
      have hgcd_dvd : d1.gcd d2 ∣ liuPaperQModulus N epsilon :=
        (Nat.gcd_dvd_left d1 d2).trans hd1dvd
      have hnu_gcd_ne : S.nu (d1.gcd d2) ≠ 0 := by
        exact (BoundingSieve.nu_pos_of_dvd_prodPrimes (s := S) hgcd_dvd).ne'
      have hnu_lcm :
          S.nu (d1.lcm d2) = S.nu d1 * S.nu d2 / S.nu (d1.gcd d2) :=
        S.nu_mult.map_lcm hnu_gcd_ne
      have hlcm_ne : d1.lcm d2 ≠ 0 :=
        Nat.lcm_ne_zero hd1pos.ne' hd2pos.ne'
      have hrecip :
          S.nu (d1.lcm d2) = 1 / Nat.totient (d1.lcm d2) := by
        simp [S, liuSelbergBoundingSieve, liuSelbergReciprocalTotient, hlcm_ne]
      calc
        S.nu d1 * lambda d1 * S.nu d2 * lambda d2 * (S.nu (d1.gcd d2))⁻¹ =
            lambda d1 * lambda d2 * (S.nu d1 * S.nu d2 / S.nu (d1.gcd d2)) := by
          ring
        _ = lambda d1 * lambda d2 * S.nu (d1.lcm d2) := by rw [← hnu_lcm]
        _ = lambda d1 * lambda d2 / Nat.totient (d1.lcm d2) := by
          simp [hrecip, div_eq_mul_inv, mul_assoc, mul_comm]
    _ = liuSelbergCoefficientFactor N epsilon lambda :=
      fullDivisors_quadraticSum_eq_liuSelbergCoefficientFactor_of_support hlambda

/-- Under the source support hypotheses and `Even N`, the Selberg coefficient
factor is the diagonal main sum of a `BoundingSieve` with `ν(d) = 1/φ(d)`. -/
theorem liuSelbergCoefficientFactor_eq_mainSum_lambdaSquared
    {N : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hNeven : Even N) (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda) :
    (liuSelbergBoundingSieve N epsilon hNeven).mainSum
        (BoundingSieve.lambdaSquared lambda) =
      liuSelbergCoefficientFactor N epsilon lambda :=
  liuSelbergCoefficientFactor_eq_mainSum_lambdaSquared_of_support hNeven hlambda.1

/-- The admissible-weight specialization of the support-only carrier identity. -/
theorem fullDivisors_quadraticSum_eq_liuSelbergCoefficientFactor
    {N : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda) :
    (liuPaperQModulus N epsilon).divisors.sum (fun d1 =>
      (liuPaperQModulus N epsilon).divisors.sum (fun d2 =>
        lambda d1 * lambda d2 / Nat.totient (Nat.lcm d1 d2))) =
      liuSelbergCoefficientFactor N epsilon lambda :=
  fullDivisors_quadraticSum_eq_liuSelbergCoefficientFactor_of_support hlambda.1

/-- Under the source support hypotheses and `Even N`, the Selberg coefficient
factor is a nonnegative diagonal sum of squares. -/
theorem liuSelbergCoefficientFactor_nonneg_of_admissible_even
    {N : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hNeven : Even N) (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda) :
    0 ≤ liuSelbergCoefficientFactor N epsilon lambda := by
  rw [← liuSelbergCoefficientFactor_eq_mainSum_lambdaSquared hNeven hlambda]
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq
      (s := liuSelbergBoundingSieve N epsilon hNeven) lambda]
  apply Finset.sum_nonneg
  intro l hl
  have hpos :
      0 < (liuSelbergBoundingSieve N epsilon hNeven).selbergTerms l := by
    exact BoundingSieve.selbergTerms_pos
      (s := liuSelbergBoundingSieve N epsilon hNeven)
      ((Nat.mem_divisors.mp hl).1)
  exact mul_nonneg (inv_nonneg.mpr hpos.le) (sq_nonneg _)

/-- Exact finite factorization of Liu's arbitrary-model Selberg main term. -/
theorem liuSelbergMainTerm_eq_coefficientFactor_mul_weightMainSum
    (main : ℝ → ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) :
    liuSelbergMainTerm main N epsilon lambda =
      liuSelbergCoefficientFactor N epsilon lambda * liuWeightMainSum main N := by
  classical
  unfold liuSelbergMainTerm liuSelbergCoefficientFactor liuWeightMainSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d1 _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d2 _
  ring

/-- Source-facing specialization of the finite factorization to Liu's genuine
logarithmic-integral family. -/
theorem liuSelbergMainTerm_logarithmicIntegral_eq
    (kappa : ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) :
    liuSelbergMainTerm (liuLogarithmicIntegral kappa) N epsilon lambda =
      liuSelbergCoefficientFactor N epsilon lambda *
        liuWeightMainSum (liuLogarithmicIntegral kappa) N :=
  liuSelbergMainTerm_eq_coefficientFactor_mul_weightMainSum
    (liuLogarithmicIntegral kappa) N epsilon lambda

/-- The sharp source Selberg coefficient upper estimate needed for Liu's `M₁`.
Its sign is a theorem, not part of this input. -/
def LiuSelbergCoefficientFactorBound
    (delta : ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : Prop :=
  liuSelbergCoefficientFactor N epsilon lambda ≤
    (8 + delta) *
      MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N / Real.log N

/-- Multiplying the two component estimates gives the `M₁` coefficient
`(8 + delta) * K`, with no numerical approximation. -/
theorem liuSelbergMainTerm_le_of_componentBounds
    (kappa delta K : ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ)
    (hNeven : Even N)
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda)
    (hdelta : 0 ≤ 8 + delta)
    (hseries :
      0 ≤ MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N)
    (hlog : 0 < Real.log N)
    (hcoefficient :
      LiuSelbergCoefficientFactorBound delta N epsilon lambda)
    (hweight : LiuGenuineLiWeightMainSumBound kappa K N) :
    liuSelbergMainTerm (liuLogarithmicIntegral kappa) N epsilon lambda ≤
      (8 + delta) * K *
        MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
        (N : ℝ) / Real.log N ^ 2 := by
  rw [liuSelbergMainTerm_logarithmicIntegral_eq]
  have hcoefficient_nonneg :
      0 ≤ liuSelbergCoefficientFactor N epsilon lambda :=
    liuSelbergCoefficientFactor_nonneg_of_admissible_even hNeven hlambda
  calc
    liuSelbergCoefficientFactor N epsilon lambda *
          liuWeightMainSum (liuLogarithmicIntegral kappa) N ≤
        ((8 + delta) *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N /
            Real.log N) *
          (K * (N : ℝ) / Real.log N) := by
      exact mul_le_mul hcoefficient hweight.2 hweight.1
        (div_nonneg (mul_nonneg hdelta hseries) hlog.le)
    _ = (8 + delta) * K *
          MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log N ^ 2 := by
      field_simp

/-- Exact decimal margin after writing `K = 0.49254 + eta`: the base product is
`3.94032`, leaving precisely `0.00001` for the linear and quadratic errors. -/
theorem liuM1_threePointNineFourZeroThreeThree_margin
    (delta eta : ℝ)
    (hmargin :
      8 * eta + 0.49254 * delta + delta * eta ≤ 0.00001) :
    (8 + delta) * (0.49254 + eta) ≤ 3.94033 := by
  nlinarith

/-- A version of the exact margin allowing any `K ≤ 0.49254 + eta`. -/
theorem liuM1_threePointNineFourZeroThreeThree_margin_of_K_le
    (delta eta K : ℝ) (hdelta : 0 ≤ 8 + delta)
    (hK : K ≤ 0.49254 + eta)
    (hmargin :
      8 * eta + 0.49254 * delta + delta * eta ≤ 0.00001) :
    (8 + delta) * K ≤ 3.94033 := by
  calc
    (8 + delta) * K ≤ (8 + delta) * (0.49254 + eta) :=
      mul_le_mul_of_nonneg_left hK hdelta
    _ ≤ 3.94033 :=
      liuM1_threePointNineFourZeroThreeThree_margin delta eta hmargin

namespace LiuSelbergMainTermUpperBound

/-- The printed `3.94033` bound follows only from the two explicit analytic
component hypotheses, positivity, and the exact finite-algebra margin. -/
theorem of_componentBounds
    (kappa delta eta K : ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ)
    (hNeven : Even N)
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda)
    (hdelta : 0 ≤ 8 + delta)
    (hseries :
      0 ≤ MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N)
    (hlog : 0 < Real.log N)
    (hK : K ≤ 0.49254 + eta)
    (hmargin :
      8 * eta + 0.49254 * delta + delta * eta ≤ 0.00001)
    (hcoefficient :
      LiuSelbergCoefficientFactorBound delta N epsilon lambda)
    (hweight : LiuGenuineLiWeightMainSumBound kappa K N) :
    LiuSelbergMainTermUpperBound kappa N epsilon lambda := by
  have hcoefficientValue :
      (8 + delta) * K ≤ (3.94033 : ℝ) :=
    liuM1_threePointNineFourZeroThreeThree_margin_of_K_le
      delta eta K hdelta hK hmargin
  unfold LiuSelbergMainTermUpperBound
  calc
    liuSelbergMainTerm (liuLogarithmicIntegral kappa) N epsilon lambda ≤
        (8 + delta) * K *
          MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log N ^ 2 :=
      liuSelbergMainTerm_le_of_componentBounds
        kappa delta K N epsilon lambda hNeven hlambda
        hdelta hseries hlog hcoefficient hweight
    _ ≤ 3.94033 *
          MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log N ^ 2 := by
      have hscale :
          0 ≤ MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 := by
        positivity
      calc
        (8 + delta) * K *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 =
            ((8 + delta) * K) *
              (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
                (N : ℝ) / Real.log N ^ 2) := by ring
        _ ≤ 3.94033 *
              (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
                (N : ℝ) / Real.log N ^ 2) :=
          mul_le_mul_of_nonneg_right hcoefficientValue hscale
        _ = 3.94033 *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 := by ring

end LiuSelbergMainTermUpperBound

end MathlibNt.SieveTheory.LiuWeight
