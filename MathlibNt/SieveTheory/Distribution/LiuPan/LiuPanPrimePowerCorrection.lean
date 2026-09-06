import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanSignedResidualSplit
import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainSum
import Mathlib.NumberTheory.Chebyshev

/-!
# Global bound for Liu's AP prime-power correction

This module bounds the progression-restricted correction by the unrestricted
nonprime von Mangoldt sum. On nonzero von Mangoldt support, `n >= 2`, so the
normalizing logarithm is bounded below by the exact constant `log 2`.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve
open ArithmeticFunction

/-- The unrestricted nonprime von Mangoldt sum with the logarithmic
normalization occurring in the prime-power correction. -/
noncomputable def globalPrimePowerCorrection (y : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n / Real.log (n : ℝ)

private theorem nat_log_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  exact Real.log_natCast_nonneg n

private theorem globalPrimePowerCorrection_term_le (n : ℕ) :
    (if n.Prime then 0 else Λ n / Real.log (n : ℝ)) ≤
      (if n.Prime then 0 else Λ n / Real.log 2) := by
  by_cases hp : n.Prime
  · simp [hp]
  simp only [hp, if_false]
  by_cases hΛ : Λ n = 0
  · simp [hΛ]
  have hn : 2 ≤ n := IsPrimePow.two_le (vonMangoldt_ne_zero_iff.mp hΛ)
  exact div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.log_pos one_lt_two)
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))

/-- Removing the congruence restriction only enlarges the nonnegative
prime-power correction. This includes the degenerate moduli `q = 0, 1`. -/
theorem apPrimePowerCorrection_le_global (y q l : ℕ) :
    apPrimePowerCorrection y q l ≤ globalPrimePowerCorrection y := by
  unfold apPrimePowerCorrection globalPrimePowerCorrection
  apply sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · simp [hp]
  simp only [hp, if_false]
  by_cases hmod : n ≡ l [MOD q]
  · simp [hmod]
  · simp only [hmod, if_false]
    exact div_nonneg vonMangoldt_nonneg (nat_log_nonneg n)

/-- Modulo one the progression restriction disappears exactly. -/
theorem apPrimePowerCorrection_mod_one (y l : ℕ) :
    apPrimePowerCorrection y 1 l = globalPrimePowerCorrection y := by
  simp [apPrimePowerCorrection, globalPrimePowerCorrection, Nat.modEq_one]

/-- The zero-modulus term in Liu's outer average is killed by its squared
Möbius weight, independently of the residue convention modulo zero. -/
theorem liuPanPrimePower_modulusWeight_zero :
    ((((ArithmeticFunction.moebius 0 : ℤ) : ℝ) ^ 2) *
     (3 : ℝ) ^ (0 : ℕ).primeFactors.card) = 0 := by
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree not_squarefree_zero]
  norm_num

private theorem sum_not_prime_vonMangoldt_eq_psi_sub_theta (y : ℕ) :
    (∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n) =
      Chebyshev.psi y - Chebyshev.theta y := by
  have h := Chebyshev.psi_sub_theta_eq_sum_not_prime (y : ℝ)
  rw [Nat.floor_natCast] at h
  rw [h, Nat.range_succ_eq_Icc_zero]
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le y)]
  simp [sum_filter]

/-- The unrestricted correction is at most the Chebyshev prime-power tail
divided by the exact lower bound `log 2` for its denominator. -/
theorem globalPrimePowerCorrection_le_psi_sub_theta (y : ℕ) :
    globalPrimePowerCorrection y ≤
      (Chebyshev.psi y - Chebyshev.theta y) / Real.log 2 := by
  unfold globalPrimePowerCorrection
  calc
    (∑ n ∈ range (y + 1), if n.Prime then 0 else
        Λ n / Real.log (n : ℝ)) ≤
        ∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n / Real.log 2 := by
      apply sum_le_sum
      intro n hn
      exact globalPrimePowerCorrection_term_le n
    _ = (∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n) / Real.log 2 := by
      rw [sum_div]
      apply sum_congr rfl
      intro n hn
      by_cases hp : n.Prime <;> simp [hp]
    _ = (Chebyshev.psi y - Chebyshev.theta y) / Real.log 2 := by
      rw [sum_not_prime_vonMangoldt_eq_psi_sub_theta]

/-- The AP correction is bounded by the same Chebyshev tail, uniformly in the
modulus and residue. -/
theorem apPrimePowerCorrection_le_psi_sub_theta (y q l : ℕ) :
    apPrimePowerCorrection y q l ≤
      (Chebyshev.psi y - Chebyshev.theta y) / Real.log 2 :=
  (apPrimePowerCorrection_le_global y q l).trans
    (globalPrimePowerCorrection_le_psi_sub_theta y)

/-- The global correction is nonnegative, including at `y = 0, 1`. -/
theorem globalPrimePowerCorrection_nonneg (y : ℕ) :
    0 ≤ globalPrimePowerCorrection y :=
  (apPrimePowerCorrection_nonneg y 1 0).trans
    (apPrimePowerCorrection_le_global y 1 0)

/-- Effective Chebyshev control gives a nonnegative constant for which the
global logarithmically normalized correction is `O(sqrt y)`. -/
theorem exists_globalPrimePowerCorrection_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ,
      globalPrimePowerCorrection y ≤ C * Real.sqrt y := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := max C 0 / Real.log 2
  refine ⟨D,
    div_nonneg (le_max_right C 0) (le_of_lt (Real.log_pos one_lt_two)), ?_⟩
  intro y
  calc
    globalPrimePowerCorrection y ≤
        (Chebyshev.psi y - Chebyshev.theta y) / Real.log 2 :=
      globalPrimePowerCorrection_le_psi_sub_theta y
    _ ≤ (max C 0 * Real.sqrt y) / Real.log 2 := by
      apply (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).2
      exact (hC (y : ℝ)).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
    _ = D * Real.sqrt y := by
      dsimp [D]
      ring

/-- Asymptotic form of the effective global correction bound. -/
theorem globalPrimePowerCorrection_isBigO_sqrt :
    globalPrimePowerCorrection =O[atTop]
      (fun y : ℕ => Real.sqrt y) := by
  rw [Asymptotics.isBigO_iff]
  obtain ⟨C, hC, h⟩ := exists_globalPrimePowerCorrection_le_sqrt
  refine ⟨C, Filter.Eventually.of_forall fun y => ?_⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg (globalPrimePowerCorrection_nonneg y),
    abs_of_nonneg (Real.sqrt_nonneg _)] using h y

/-! ## Lifting the global estimate through Liu's finite maxima -/

/-- The exact Liu-weight support functional left by the global square-root
estimate. The source weight is retained as `|f a|`. -/
noncomputable def liuPanPrimePowerSqrtSupport
    (y X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 X, |f a| * Real.sqrt (y / a : ℕ)

/-- The square-root mass of Liu's exact source pair set. -/
noncomputable def liuPanPrimePowerPairSqrtMass (N : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    Real.sqrt (N / (p.1 * p.2) : ℕ)

/-- For Liu's characteristic source weight, the support functional is exactly
the square-root mass of the unique admissible prime-pair representations. -/
theorem liuPanPrimePowerSqrtSupport_source_eq_pairSqrtMass (N : ℕ) :
    liuPanPrimePowerSqrtSupport N N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
      liuPanPrimePowerPairSqrtMass N := by
  classical
  unfold liuPanPrimePowerSqrtSupport liuPanPrimePowerPairSqrtMass
  calc
    (∑ a ∈ Icc 1 N,
        |liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a| *
          Real.sqrt (N / a : ℕ)) =
      ∑ a ∈ (Icc 1 N).filter
          (LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N)),
        Real.sqrt (N / a : ℕ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a ha
      by_cases hs : LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N) a
      · simp [liuWeight, hs]
      · simp [liuWeight, hs]
    _ = ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
        Real.sqrt (N / (p.1 * p.2) : ℕ) := by
      symm
      apply sum_bij (fun p _ => p.1 * p.2)
      · intro p hp
        rw [mem_filter, mem_Icc]
        exact ⟨⟨liuWeightPairs_product_pos hp,
          liuWeightSupport_le ⟨p, hp, rfl⟩⟩, ⟨p, hp, rfl⟩⟩
      · intro p hp q hq hpq
        have hu := liuPairConditions_unique
          (mem_liuWeightPairs.mp hp) (mem_liuWeightPairs.mp hq) hpq
        exact Prod.ext hu.1 hu.2
      · intro a ha
        rcases (mem_filter.mp ha).2 with ⟨p, hp, hpa⟩
        exact ⟨p, hp, hpa⟩
      · intro p hp
        rfl

/-- Cauchy--Schwarz reduces the source pair square-root mass to the exact pair
cardinality and the already controlled reciprocal pair mass. -/
theorem liuPanPrimePowerPairSqrtMass_sq_le (N : ℕ) :
    liuPanPrimePowerPairSqrtMass N ^ 2 ≤
      (liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card *
        ((N : ℝ) * liuWeightPairReciprocalSum N) := by
  classical
  let P := liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)
  calc
    liuPanPrimePowerPairSqrtMass N ^ 2 =
        (∑ p ∈ P, (1 : ℝ) * Real.sqrt (N / (p.1 * p.2) : ℕ)) ^ 2 := by
      simp [liuPanPrimePowerPairSqrtMass, P]
    _ ≤ (∑ p ∈ P, (1 : ℝ) ^ 2) *
        ∑ p ∈ P, (Real.sqrt (N / (p.1 * p.2) : ℕ)) ^ 2 :=
      sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℝ))
        (fun p => Real.sqrt (N / (p.1 * p.2) : ℕ))
    _ = (P.card : ℝ) *
        ∑ p ∈ P, ((N / (p.1 * p.2) : ℕ) : ℝ) := by
      simp only [one_pow, sum_const, nsmul_eq_mul, mul_one,
        Real.sq_sqrt (Nat.cast_nonneg _)]
    _ ≤ (P.card : ℝ) *
        ∑ p ∈ P, (N : ℝ) / (p.1 * p.2 : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro p hp
      exact Nat.cast_div_le
    _ = (liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card *
        ((N : ℝ) * liuWeightPairReciprocalSum N) := by
      simp only [P]
      congr 1
      unfold liuWeightPairReciprocalSum
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      simp only [Nat.cast_mul]
      ring

theorem liuPanPrimePowerSqrtSupport_nonneg
    (y X : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuPanPrimePowerSqrtSupport y X f := by
  unfold liuPanPrimePowerSqrtSupport
  exact sum_nonneg fun a ha =>
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem liuPanPrimePowerSqrtSupport_mono
    {y x X : ℕ} (hyx : y ≤ x) (f : ℕ → ℝ) :
    liuPanPrimePowerSqrtSupport y X f ≤
      liuPanPrimePowerSqrtSupport x X f := by
  unfold liuPanPrimePowerSqrtSupport
  apply sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.div_le_div_right hyx

theorem liuPanSignedCorrectionKernel_le_global
    (y a q l : ℕ) :
    liuPanSignedCorrectionKernel y a q l ≤
      globalPrimePowerCorrection (y / a) :=
  apPrimePowerCorrection_le_global _ _ _

theorem liuPanSignedCorrectionBound_le_global
    (y X q l : ℕ) (f : ℕ → ℝ) :
    liuPanSignedCorrectionBound y X q l f ≤
      ∑ a ∈ Icc 1 X, |f a| * globalPrimePowerCorrection (y / a) := by
  unfold liuPanSignedCorrectionBound
  apply sum_le_sum
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop]
    exact mul_le_mul_of_nonneg_left
      (liuPanSignedCorrectionKernel_le_global y a q l) (abs_nonneg _)
  · simp only [if_neg hcop]
    exact mul_nonneg (abs_nonneg _)
      (globalPrimePowerCorrection_nonneg (y / a))

theorem liuPanSignedCorrectionBound_le_sqrtSupport
    {C : ℝ}
    (hglobal : ∀ t : ℕ,
      globalPrimePowerCorrection t ≤ C * Real.sqrt t)
    (y X q l : ℕ) (f : ℕ → ℝ) :
    liuPanSignedCorrectionBound y X q l f ≤
      C * liuPanPrimePowerSqrtSupport y X f := by
  calc
    liuPanSignedCorrectionBound y X q l f ≤
        ∑ a ∈ Icc 1 X, |f a| * globalPrimePowerCorrection (y / a) :=
      liuPanSignedCorrectionBound_le_global y X q l f
    _ ≤ ∑ a ∈ Icc 1 X,
        |f a| * (C * Real.sqrt (y / a : ℕ)) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hglobal (y / a)) (abs_nonneg _)
    _ = C * liuPanPrimePowerSqrtSupport y X f := by
      simp only [liuPanPrimePowerSqrtSupport, mul_sum, mul_left_comm]

theorem liuPanAPPrimePowerCorrectionMaxL_le_sqrtSupport
    {C : ℝ} (hC : 0 ≤ C)
    (hglobal : ∀ t : ℕ,
      globalPrimePowerCorrection t ≤ C * Real.sqrt t)
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAPPrimePowerCorrectionMaxL y X q f ≤
      C * liuPanPrimePowerSqrtSupport y X f := by
  unfold liuPanAPPrimePowerCorrectionMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · rw [dif_pos hS]
    apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨l, hl, rfl⟩
    exact liuPanSignedCorrectionBound_le_sqrtSupport
      hglobal y X q l f
  · rw [dif_neg hS]
    exact mul_nonneg hC (liuPanPrimePowerSqrtSupport_nonneg y X f)

theorem liuPanAPPrimePowerCorrectionMaxY_le_sqrtSupport
    {C : ℝ} (hC : 0 ≤ C)
    (hglobal : ∀ t : ℕ,
      globalPrimePowerCorrection t ≤ C * Real.sqrt t)
    (X q x : ℕ) (f : ℕ → ℝ) :
    liuPanAPPrimePowerCorrectionMaxY X q x f ≤
      C * liuPanPrimePowerSqrtSupport x X f := by
  unfold liuPanAPPrimePowerCorrectionMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyx : y ≤ x := by
    simp only [mem_range] at hy
    omega
  exact (liuPanAPPrimePowerCorrectionMaxL_le_sqrtSupport
    hC hglobal y X q f).trans
      (mul_le_mul_of_nonneg_left
        (liuPanPrimePowerSqrtSupport_mono hyx f) hC)

/-- The exact finite support and modulus-weight functional remaining after the
global Chebyshev estimate. No bound on the source weight is inserted here. -/
noncomputable def liuPanPrimePowerModulusWeightMass
    (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card

noncomputable def liuMainPanPrimePowerSqrtSupport
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanPrimePowerSqrtSupport N N f

/-- The remaining global-support functional factors exactly into a modulus
weight mass and the source support mass. -/
theorem liuMainPanPrimePowerSqrtSupport_eq_mul
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) :
    liuMainPanPrimePowerSqrtSupport N f B =
      liuPanPrimePowerModulusWeightMass N B *
        liuPanPrimePowerSqrtSupport N N f := by
  unfold liuMainPanPrimePowerSqrtSupport
    liuPanPrimePowerModulusWeightMass
  rw [sum_mul]

/-- Source specialization of the exact factorization: the only remaining
inputs are the modulus weight mass and Liu's pair square-root mass. -/
theorem liuMainPanPrimePowerSqrtSupport_source_eq_mul
    (N : ℕ) (B : ℝ) :
    liuMainPanPrimePowerSqrtSupport N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B =
      liuPanPrimePowerModulusWeightMass N B *
        liuPanPrimePowerPairSqrtMass N := by
  rw [liuMainPanPrimePowerSqrtSupport_eq_mul,
    liuPanPrimePowerSqrtSupport_source_eq_pairSqrtMass]

theorem liuMainPanAPPrimePowerCorrection_average_le_sqrtSupport
    {C : ℝ} (hC : 0 ≤ C)
    (hglobal : ∀ t : ℕ,
      globalPrimePowerCorrection t ≤ C * Real.sqrt t)
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) :
    (∑ q ∈ range (panModulusCutoff N B + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
        liuPanAPPrimePowerCorrectionMaxY N q N f) ≤
      C * liuMainPanPrimePowerSqrtSupport N f B := by
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
        liuPanAPPrimePowerCorrectionMaxY N q N f) ≤
        ∑ q ∈ range (panModulusCutoff N B + 1),
          (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ q.primeFactors.card *
            (C * liuPanPrimePowerSqrtSupport N N f) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (liuPanAPPrimePowerCorrectionMaxY_le_sqrtSupport
          hC hglobal N q N f) (panTypeI_weight_nonneg q)
    _ = C * liuMainPanPrimePowerSqrtSupport N f B := by
      simp only [liuMainPanPrimePowerSqrtSupport, mul_sum, mul_left_comm]

/-- An explicit bound for the remaining finite support functional is exactly
the additional input needed to close the existing fixed-`N` correction bound. -/
theorem LiuMainPanAPPrimePowerCorrectionBoundAt.of_sqrtSupport
    {C K : ℝ} (hC : 0 ≤ C)
    (hglobal : ∀ t : ℕ,
      globalPrimePowerCorrection t ≤ C * Real.sqrt t)
    {N : ℕ} {f : ℕ → ℝ} {A B : ℝ}
    (hsupport :
      liuMainPanPrimePowerSqrtSupport N f B ≤
        K * N / Real.log N ^ A) :
    LiuMainPanAPPrimePowerCorrectionBoundAt N f A B (C * K) := by
  unfold LiuMainPanAPPrimePowerCorrectionBoundAt
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
        liuPanAPPrimePowerCorrectionMaxY N q N f) ≤
        C * liuMainPanPrimePowerSqrtSupport N f B :=
      liuMainPanAPPrimePowerCorrection_average_le_sqrtSupport
        hC hglobal N f B
    _ ≤ C * (K * N / Real.log N ^ A) :=
      mul_le_mul_of_nonneg_left hsupport hC
    _ = (C * K) * N / Real.log N ^ A := by ring

end MathlibNt.SieveTheory.LiuWeight
