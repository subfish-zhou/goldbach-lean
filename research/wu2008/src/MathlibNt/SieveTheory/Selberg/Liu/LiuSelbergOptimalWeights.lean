import MathlibNt.SieveTheory.Selberg.TruncatedOptimalWeights
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergCoefficient
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

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

private lemma sum_moebius_eq_one {n : ℕ} :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then (1 : ℝ) else 0 := by
  have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
  have hkey : (ζ * (μ : ArithmeticFunction ℝ)) n =
      (1 : ArithmeticFunction ℝ) n := by rw [h]
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
  simpa [ArithmeticFunction.intCoe_apply, mul_comm] using hkey
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

/-- The reciprocal truncated Selberg denominator is a lower bound for every
normalized weight supported on the truncated carrier. -/
theorem one_div_truncatedSelbergDenominator_le_mainSum
    (S : BoundingSieve) {R : ℕ} (w : ℕ → ℝ)
    (hw_one : w 1 = 1)
    (hw_support : ∀ {d : ℕ}, w d ≠ 0 → d ∈ truncatedSelbergCarrier S R) :
    1 / truncatedSelbergDenominator S R ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  let C := truncatedSelbergCarrier S R
  let x : ℕ → ℝ := fun l =>
    ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0
  have hC_subset : C ⊆ S.prodPrimes.divisors := by
    intro d hd
    exact (Finset.mem_filter.mp hd).1
  have hx_zero : ∀ l ∈ S.prodPrimes.divisors, l ∉ C → x l = 0 := by
    intro l hlP hlC
    apply Finset.sum_eq_zero
    intro d hdP
    by_cases hld : l ∣ d
    · have hwd : w d = 0 := by
        by_contra hwd
        have hdC := hw_support hwd
        apply hlC
        exact Finset.mem_filter.mpr
          ⟨hlP, (Nat.le_of_dvd
            (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdP).1
              (Nat.pos_of_ne_zero S.prodPrimes_ne_zero)) hld).trans
            (Finset.mem_filter.mp hdC).2⟩
      simp [hld, hwd]
    · simp [hld]
  have hMoebiusInvFull :
      ∑ l ∈ S.prodPrimes.divisors, (μ l : ℝ) * x l = 1 := by
    calc
      ∑ l ∈ S.prodPrimes.divisors, (μ l : ℝ) * x l =
          ∑ l ∈ S.prodPrimes.divisors,
            ∑ d ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by
            simp_rw [x, mul_sum]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            ∑ l ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (∑ l ∈ d.divisors, (μ l : ℝ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdvd : d ∣ S.prodPrimes := (Nat.mem_divisors.mp hd).1
            simp_rw [mul_ite, mul_zero]
            rw [← Finset.sum_filter,
              Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero hdvd,
              mul_sum]
            exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (if d = 1 then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [sum_moebius_eq_one]
      _ = S.nu 1 * w 1 := by
            have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
              Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
            simp_rw [mul_ite, mul_one, mul_zero]
            rw [Finset.sum_ite_eq_of_mem' _ _ _ h1mem]
      _ = 1 := by
            rw [S.nu_mult.map_one, hw_one]
            norm_num
  have hMoebiusInv : ∑ l ∈ C, (μ l : ℝ) * x l = 1 := by
    rw [← hMoebiusInvFull]
    apply Finset.sum_subset hC_subset
    intro l hlP hlC
    rw [hx_zero l hlP hlC]
    simp
  have hdiag_restrict :
      (∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ * (x l) ^ 2) =
        ∑ l ∈ C, (S.selbergTerms l)⁻¹ * (x l) ^ 2 := by
    symm
    apply Finset.sum_subset hC_subset
    intro l hlP hlC
    rw [hx_zero l hlP hlC]
    simp
  have hTitu :
      (∑ l ∈ C, (μ l : ℝ) * x l) ^ 2 /
          ∑ l ∈ C, S.selbergTerms l * (μ l : ℝ) ^ 2 ≤
        ∑ l ∈ C,
          ((μ l : ℝ) * x l) ^ 2 /
            (S.selbergTerms l * (μ l : ℝ) ^ 2) := by
    apply sq_sum_div_le_sum_sq_div
    intro l hl
    have hlP : l ∈ S.prodPrimes.divisors := hC_subset hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hlP
    have hpos := S.selbergTerms_pos (Nat.mem_divisors.mp hlP).1
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
    exact hpos
  have hDenom :
      (∑ l ∈ C, S.selbergTerms l * (μ l : ℝ) ^ 2) =
        truncatedSelbergDenominator S R := by
    change (∑ l ∈ C, S.selbergTerms l * (μ l : ℝ) ^ 2) =
      ∑ l ∈ C, S.selbergTerms l
    apply Finset.sum_congr rfl
    intro l hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes (hC_subset hl)
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
  have hRHS :
      (∑ l ∈ C, ((μ l : ℝ) * x l) ^ 2 /
          (S.selbergTerms l * (μ l : ℝ) ^ 2)) =
        ∑ l ∈ C, (S.selbergTerms l)⁻¹ * (x l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes (hC_subset hl)
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one, mul_pow, hμsq, one_mul, div_eq_inv_mul]
  rw [hMoebiusInv, hDenom] at hTitu
  simp only [one_pow] at hTitu
  rw [hRHS, one_div] at hTitu
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  change
    1 / truncatedSelbergDenominator S R ≤
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ * (x l) ^ 2
  rw [hdiag_restrict]
  simpa only [one_div] using hTitu

/-- The truncated Selberg optimizer minimizes the main sum among all normalized
weights supported on the same carrier. -/
theorem mainSum_truncatedSelbergOptimalLambda_le_mainSum
    (S : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) (w : ℕ → ℝ)
    (hw_one : w 1 = 1)
    (hw_support : ∀ {d : ℕ}, w d ≠ 0 → d ∈ truncatedSelbergCarrier S R) :
    S.mainSum (BoundingSieve.lambdaSquared (truncatedSelbergOptimalLambda S R)) ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  rw [mainSum_truncatedSelbergOptimalLambda S hR]
  exact one_div_truncatedSelbergDenominator_le_mainSum S w hw_one hw_support

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

private noncomputable def liuSelbergOptimalWeights
    (N : ℕ) (epsilon : ℝ) (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    MathlibNt.SieveTheory.SelbergUpperBound.SelbergWeights N epsilon where
  lambda := liuSelbergOptimalLambda N epsilon
  lambda_one := liuSelbergOptimalLambda_one hNeven hR
  lambda_support := by
    intro d hd
    by_contra hne
    have hs := liuSelbergOptimalLambda_support hne
    rcases hd with hlarge | hndvd
    · exact (not_lt_of_ge (by
        simpa [paperQSourceCutoff] using hs.2)) hlarge
    · apply hndvd
      rw [LegacySelberg.selbergQ_eq_liuPaperQModulus]
      exact hs.1
  lambda_bounded := fun d => abs_liuSelbergOptimalLambda_le_one hNeven hR

theorem LegacySelberg.LiuOptimizedSelbergCoefficientEstimate.of_denominatorLowerBound
    {delta epsilon : ℝ} (hdelta : 0 < 8 + delta)
    (hden : LiuSelbergDenominatorLowerBound delta epsilon) :
    LegacySelberg.LiuOptimizedSelbergCoefficientEstimate delta epsilon := by
  filter_upwards [hden, eventually_ge_atTop (2 : ℕ)] with N hdenN hN
  intro hNeven hR
  let SW := liuSelbergOptimalWeights N epsilon hNeven hR
  refine ⟨SW, ?_⟩
  unfold LiuSelbergCoefficientFactorBound
  change liuSelbergCoefficientFactor N epsilon
      (liuSelbergOptimalLambda N epsilon) ≤ _
  rw [liuSelbergCoefficientFactor_optimalLambda hNeven hR]
  exact one_div_liuSelbergDenominator_le hdelta hN hNeven hR
    (hdenN hN hNeven hR)

theorem LegacySelberg.LiuOptimizedSelbergCoefficientInput.of_denominatorLowerBound
    (hden : ∀ delta > 0, ∃ epsilon0 > 0,
      ∀ epsilon, 0 < epsilon → epsilon ≤ epsilon0 →
        LiuSelbergDenominatorLowerBound delta epsilon) :
    LegacySelberg.LiuOptimizedSelbergCoefficientInput := by
  intro delta hdelta
  obtain ⟨epsilon0, hepsilon0, hden⟩ := hden delta hdelta
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon hepsilon_le
  exact LegacySelberg.LiuOptimizedSelbergCoefficientEstimate.of_denominatorLowerBound
    (by linarith) (hden epsilon hepsilon hepsilon_le)

end MathlibNt.SieveTheory.LiuWeight
