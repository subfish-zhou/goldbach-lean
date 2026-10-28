import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergMainTerm
/-!
# Exact finite Selberg optimization for Liu's source modulus

Liu's lemma `lm-selberg` states the existence of coefficients with main term
`[8 + O(ε)] 𝔖(N) / log N`; it does not prove the finite minimization in the
form needed by this development.  This file performs that minimization exactly.
After it, the genuinely analytic missing statement is precisely the eventual,
uniform weighted Mertens--Selberg lower bound for
`∑_{l ∣ Q, l ≤ R} ∏_{p ∣ l} 1 / (p - 2)`.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset

/-- The positive local Selberg factor attached to a source divisor. -/
noncomputable def liuSelbergTerm (l : ℕ) : ℝ :=
  ∏ p ∈ l.primeFactors, ((p : ℝ) - 2)⁻¹

/-- Liu's truncated Selberg denominator.  It has no proof argument. -/
noncomputable def liuSelbergDenominator (N : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ l ∈ liuSelbergLambdaSourceCarrier N epsilon, liuSelbergTerm l

/-- On the even source modulus, the explicit local factor is Mathlib's
`BoundingSieve.selbergTerms`. -/
theorem liuSelbergTerm_eq_selbergTerms
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hl : l ∣ liuPaperQModulus N epsilon) :
    liuSelbergTerm l =
      (liuSelbergBoundingSieve N epsilon hNeven).selbergTerms l := by
  let S := liuSelbergBoundingSieve N epsilon hNeven
  rw [BoundingSieve.selbergTerms_apply, ← S.prod_primeFactors_nu hl,
    ← Finset.prod_mul_distrib]
  unfold liuSelbergTerm
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpl : p ∣ l := Nat.dvd_of_mem_primeFactors hp
  have hpQ : p ∣ liuPaperQModulus N epsilon := hpl.trans hl
  have hpN : ¬p ∣ N :=
    (prime_dvd_liuPaperQModulus (N := N) (epsilon := epsilon) hpprime).mp hpQ |>.2
  have hp2 : p ≠ 2 := fun h => hpN (h.symm ▸ hNeven.two_dvd)
  have hpgt : 2 < p :=
    lt_of_le_of_ne hpprime.two_le (by simpa using hp2.symm)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (lt_trans Nat.one_lt_two hpgt)
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hpgt
  have hnu : S.nu p = ((p : ℝ) - 1)⁻¹ := by
    dsimp [S, liuSelbergBoundingSieve, liuSelbergReciprocalTotient]
    rw [if_neg hpprime.ne_zero, Nat.totient_prime hpprime]
    rw [Nat.cast_sub hpprime.one_le]
    simp [one_div]
  rw [hnu]
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hpm2' : -2 + (p : ℝ) ≠ 0 := by linarith
  field_simp [hpm1, hpm2, hpm2']
  rw [show (p : ℝ) - 1 - 1 = (p : ℝ) - 2 by ring, div_self hpm2]

/-- The explicit source denominator is the generic truncated denominator. -/
private theorem liuSelbergDenominator_eq_truncated
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N) :
    liuSelbergDenominator N epsilon =
      truncatedSelbergDenominator (liuSelbergBoundingSieve N epsilon hNeven)
        (paperQSourceCutoff N epsilon) := by
  unfold liuSelbergDenominator truncatedSelbergDenominator
  apply Finset.sum_congr rfl
  intro l hl
  exact liuSelbergTerm_eq_selbergTerms hNeven
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1

/-- Every explicit Selberg term on the source carrier is positive. -/
theorem liuSelbergTerm_pos
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hl : l ∈ liuSelbergLambdaSourceCarrier N epsilon) :
    0 < liuSelbergTerm l := by
  rw [liuSelbergTerm_eq_selbergTerms hNeven
    ((Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1)]
  exact BoundingSieve.selbergTerms_pos
    (s := liuSelbergBoundingSieve N epsilon hNeven)
    ((Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1)

/-- The denominator is positive once the truncation contains `1`. -/
theorem liuSelbergDenominator_pos
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    0 < liuSelbergDenominator N epsilon := by
  rw [liuSelbergDenominator_eq_truncated hNeven]
  exact truncatedSelbergDenominator_pos _ hR

/-- The prescribed diagonal coordinate, extended by zero off the truncation. -/
noncomputable def liuSelbergOptimalX
    (N : ℕ) (epsilon : ℝ) (l : ℕ) : ℝ :=
  if l ∈ liuSelbergLambdaSourceCarrier N epsilon then
    (μ l : ℝ) * liuSelbergTerm l / liuSelbergDenominator N epsilon
  else 0

/-- Reverse-divisor Möbius inversion of the optimal diagonal coordinates. -/
noncomputable def liuSelbergOptimalLambda
    (N : ℕ) (epsilon : ℝ) (d : ℕ) : ℝ :=
  if d ∈ liuSelbergLambdaSourceCarrier N epsilon then
    (∑ e ∈ liuSelbergLambdaSourceCarrier N epsilon,
      if d ∣ e then (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0) /
      liuSelbergReciprocalTotient d
  else 0

theorem liuSelbergOptimalLambda_eq_zero_of_not_mem
    {N d : ℕ} {epsilon : ℝ}
    (hd : d ∉ liuSelbergLambdaSourceCarrier N epsilon) :
    liuSelbergOptimalLambda N epsilon d = 0 := by
  simp [liuSelbergOptimalLambda, hd]

/-- The explicit optimizer is supported on divisors of the source modulus below
the source cutoff. -/
theorem liuSelbergOptimalLambda_support
    {N d : ℕ} {epsilon : ℝ}
    (hd : liuSelbergOptimalLambda N epsilon d ≠ 0) :
    d ∣ liuPaperQModulus N epsilon ∧ d ≤ paperQSourceCutoff N epsilon := by
  have hQ0 : liuPaperQModulus N epsilon ≠ 0 :=
    (liuPaperQModulus_squarefree N epsilon).ne_zero
  by_contra h
  apply hd
  apply liuSelbergOptimalLambda_eq_zero_of_not_mem
  intro hdmem
  apply h
  exact ⟨(Nat.mem_divisors.mp (Finset.mem_filter.mp hdmem).1).1,
    (Finset.mem_filter.mp hdmem).2⟩


/-- The source diagonal coordinates specialize the generic finite optimizer. -/
private theorem liuSelbergOptimalX_eq_truncated
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N) :
    liuSelbergOptimalX N epsilon =
      truncatedSelbergOptimalX (liuSelbergBoundingSieve N epsilon hNeven)
        (paperQSourceCutoff N epsilon) := by
  funext l
  unfold liuSelbergOptimalX truncatedSelbergOptimalX
  change (if l ∈ liuSelbergLambdaSourceCarrier N epsilon then _ else 0) =
    (if l ∈ liuSelbergLambdaSourceCarrier N epsilon then _ else 0)
  split_ifs with hl
  · rw [liuSelbergTerm_eq_selbergTerms hNeven
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1,
      liuSelbergDenominator_eq_truncated hNeven]
  · rfl

/-- Reverse-divisor inversion agrees with the same generic optimizer. -/
private theorem liuSelbergOptimalLambda_eq_truncated
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N) :
    liuSelbergOptimalLambda N epsilon =
      truncatedSelbergOptimalLambda (liuSelbergBoundingSieve N epsilon hNeven)
        (paperQSourceCutoff N epsilon) := by
  funext d
  unfold liuSelbergOptimalLambda truncatedSelbergOptimalLambda
  rw [← liuSelbergOptimalX_eq_truncated hNeven]
  rfl

set_option maxHeartbeats 800000 in
/-- Reverse-divisor inversion recovers every diagonal coordinate on the
truncated carrier. -/
theorem liuSelbergOptimalX_eq_sum_nu_mul_lambda
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hl : l ∈ liuSelbergLambdaSourceCarrier N epsilon) :
    liuSelbergOptimalX N epsilon l =
      ∑ d ∈ (liuPaperQModulus N epsilon).divisors,
        if l ∣ d then
          (liuSelbergBoundingSieve N epsilon hNeven).nu d *
            liuSelbergOptimalLambda N epsilon d
        else 0 := by
  have hprod : (liuSelbergBoundingSieve N epsilon hNeven).prodPrimes =
      liuPaperQModulus N epsilon := rfl
  simpa only [hprod, ← liuSelbergOptimalX_eq_truncated hNeven,
    ← liuSelbergOptimalLambda_eq_truncated hNeven] using
    (truncatedSelbergOptimalX_eq_sum_nu_mul_lambda
      (liuSelbergBoundingSieve N epsilon hNeven) (paperQSourceCutoff N epsilon) l hl)

/-- The reverse-divisor construction is normalized at `1`. -/
theorem liuSelbergOptimalLambda_one
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    liuSelbergOptimalLambda N epsilon 1 = 1 := by
  rw [liuSelbergOptimalLambda_eq_truncated hNeven]
  exact truncatedSelbergOptimalLambda_one _ hR

/-- The diagonal coordinate identity also holds off the truncation: both sides
vanish there. -/
theorem sum_nu_mul_liuSelbergOptimalLambda_eq_optimalX
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hlQ : l ∣ liuPaperQModulus N epsilon) :
    (∑ d ∈ (liuPaperQModulus N epsilon).divisors,
      if l ∣ d then
        (liuSelbergBoundingSieve N epsilon hNeven).nu d *
          liuSelbergOptimalLambda N epsilon d
      else 0) =
      liuSelbergOptimalX N epsilon l := by
  have hprod : (liuSelbergBoundingSieve N epsilon hNeven).prodPrimes =
      liuPaperQModulus N epsilon := rfl
  simpa only [hprod, ← liuSelbergOptimalX_eq_truncated hNeven,
    ← liuSelbergOptimalLambda_eq_truncated hNeven] using
    (sum_nu_mul_truncatedSelbergOptimalLambda_eq_optimalX
      (liuSelbergBoundingSieve N epsilon hNeven) (paperQSourceCutoff N epsilon) l hlQ)

/-- Exact finite Selberg minimization: the source quadratic coefficient of the
explicit optimizer is the reciprocal truncated denominator. -/
theorem liuSelbergCoefficientFactor_optimalLambda
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    liuSelbergCoefficientFactor N epsilon
        (liuSelbergOptimalLambda N epsilon) =
      1 / liuSelbergDenominator N epsilon := by
  rw [← liuSelbergCoefficientFactor_eq_mainSum_lambdaSquared_of_support
    hNeven (fun d hd => liuSelbergOptimalLambda_support hd),
    liuSelbergOptimalLambda_eq_truncated hNeven,
    mainSum_truncatedSelbergOptimalLambda _ hR,
    ← liuSelbergDenominator_eq_truncated hNeven]

/-- Every finite optimal coefficient has the classical Selberg bound. -/
theorem abs_liuSelbergOptimalLambda_le_one
    {N d : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    |liuSelbergOptimalLambda N epsilon d| ≤ 1 := by
  rw [liuSelbergOptimalLambda_eq_truncated hNeven]
  exact abs_truncatedSelbergOptimalLambda_le_one _ hR

/-- The sole analytic statement left by the finite minimization: uniformly for
large `N`, the truncated weighted divisor sum dominates the sharp reciprocal
scale.  This is a lower bound on `G`, not the desired coefficient conclusion. -/
def LiuSelbergDenominatorLowerBound (delta epsilon : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, 2 ≤ N → Even N →
    1 ≤ paperQSourceCutoff N epsilon →
      Real.log N /
          ((8 + delta) *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N) ≤
        liuSelbergDenominator N epsilon

theorem one_div_liuSelbergDenominator_le
    {delta epsilon : ℝ} {N : ℕ}
    (hdelta : 0 < 8 + delta) (hN : 2 ≤ N) (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon)
    (hden :
      Real.log N /
          ((8 + delta) *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N) ≤
        liuSelbergDenominator N epsilon) :
    1 / liuSelbergDenominator N epsilon ≤
      (8 + delta) *
        MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N / Real.log N := by
  have hG : 0 < liuSelbergDenominator N epsilon :=
    liuSelbergDenominator_pos hNeven hR
  have hlog : 0 < Real.log N := Real.log_pos <| by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN)
  have hseries :
      0 < MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N :=
    MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N
  have hscale :
      0 < (8 + delta) *
        MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N :=
    mul_pos hdelta hseries
  apply (le_div_iff₀ hlog).2
  have hquot :
      Real.log N / liuSelbergDenominator N epsilon ≤
        (8 + delta) *
          MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N := by
    apply (div_le_iff₀ hG).2
    have := (div_le_iff₀ hscale).mp hden
    simpa [mul_comm] using this
  simpa [div_eq_mul_inv, mul_comm] using hquot


end MathlibNt.SieveTheory.LiuWeight
