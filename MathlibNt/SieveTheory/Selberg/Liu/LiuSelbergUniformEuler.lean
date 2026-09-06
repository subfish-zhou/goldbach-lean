import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergDenominatorHarmonic
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Uniform Euler controls for Liu's Selberg correction

The finite factors below isolate the dependence on the prime divisors of the
even integer `N`; the infinite factor is fixed once and for all at `N = 2`.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset Filter
open MathlibNt.SieveTheory.SingularSeries

/-- The finite Euler factor which records the prime divisors of `N`. -/
noncomputable def liuPrimeDivisorProduct (N : ℕ) : ℝ :=
  N.primeFactors.prod (fun p => 1 + ((p : ℝ)⁻¹))

/-- The absolute local Euler factor at the fixed even integer `2`. -/
noncomputable def liuUniversalAbsEulerFactor (p : Nat.Primes) : ℝ :=
  1 + liuSelbergAbsPrimeDeviation 2 p

/-- The universal absolute Euler product, independent of `N`. -/
noncomputable def liuUniversalAbsEuler : ℝ :=
  ∏' p : Nat.Primes, liuUniversalAbsEulerFactor p

/-- A fixed logarithmic absolute moment.  It is independent of the variable
integer `N` in the uniform estimates below. -/
noncomputable def liuUniversalAbsLogMoment : ℝ :=
  ∑' d : ℕ, |liuSelbergCorrection 2 d| * Real.log d

theorem summable_liuUniversalAbsEulerDeviation :
    Summable (liuSelbergAbsPrimeDeviation 2) :=
  summable_liuSelbergAbsPrimeDeviation (by norm_num) (by norm_num)

theorem liuSelbergAbsPrimeDeviation_two_nonneg (p : Nat.Primes) :
    0 ≤ liuSelbergAbsPrimeDeviation 2 p := by
  exact liuSelbergAbsPrimeDeviation_nonneg_core (by norm_num) p

theorem liuUniversalAbsEulerFactor_nonneg (p : Nat.Primes) :
    0 ≤ liuUniversalAbsEulerFactor p := by
  unfold liuUniversalAbsEulerFactor
  linarith [liuSelbergAbsPrimeDeviation_two_nonneg p]

theorem liuUniversalAbsEulerFactor_pos (p : Nat.Primes) :
    0 < liuUniversalAbsEulerFactor p := by
  unfold liuUniversalAbsEulerFactor
  linarith [liuSelbergAbsPrimeDeviation_two_nonneg p]

theorem multipliable_liuUniversalAbsEulerFactor :
    Multipliable liuUniversalAbsEulerFactor := by
  change Multipliable (fun p : Nat.Primes =>
    1 + liuSelbergAbsPrimeDeviation 2 p)
  exact Real.multipliable_one_add_of_summable
    summable_liuUniversalAbsEulerDeviation

theorem liuUniversalAbsEuler_nonneg : 0 ≤ liuUniversalAbsEuler := by
  unfold liuUniversalAbsEuler
  apply ge_of_tendsto multipliable_liuUniversalAbsEulerFactor.hasProd
  filter_upwards [] with s
  exact Finset.prod_nonneg fun p _ => liuUniversalAbsEulerFactor_nonneg p

theorem liuUniversalAbsEuler_ne_zero : liuUniversalAbsEuler ≠ 0 := by
  unfold liuUniversalAbsEuler liuUniversalAbsEulerFactor
  apply tprod_one_add_ne_zero_of_summable
  · intro p
    exact ne_of_gt (liuUniversalAbsEulerFactor_pos p)
  · apply summable_liuUniversalAbsEulerDeviation.congr
    intro p
    rw [Real.norm_eq_abs,
      abs_of_nonneg (liuSelbergAbsPrimeDeviation_two_nonneg p)]

theorem liuUniversalAbsEuler_pos : 0 < liuUniversalAbsEuler :=
  lt_of_le_of_ne liuUniversalAbsEuler_nonneg liuUniversalAbsEuler_ne_zero.symm

noncomputable def liuAbsoluteEulerFactor (N : ℕ) (p : Nat.Primes) : ℝ :=
  1 + liuSelbergAbsPrimeDeviation N p

noncomputable def liuPrimeDivisorKernel (N : ℕ) (p : Nat.Primes) : ℝ :=
  if (p : ℕ) ∣ N then 1 + ((p : ℝ)⁻¹) else 1

theorem liuSelbergAbsPrimeDeviation_nonneg
    {N : ℕ} (_hNeven : Even N) (p : Nat.Primes) :
    0 ≤ liuSelbergAbsPrimeDeviation N p := by
  exact liuSelbergAbsPrimeDeviation_nonneg_core _hNeven p

theorem liuAbsoluteEulerFactor_one_le
    {N : ℕ} (hNeven : Even N) (p : Nat.Primes) :
    1 ≤ liuAbsoluteEulerFactor N p := by
  unfold liuAbsoluteEulerFactor
  linarith [liuSelbergAbsPrimeDeviation_nonneg hNeven p]

theorem multipliable_liuAbsoluteEulerFactor
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Multipliable (liuAbsoluteEulerFactor N) := by
  change Multipliable (fun p : Nat.Primes =>
    1 + liuSelbergAbsPrimeDeviation N p)
  exact Real.multipliable_one_add_of_summable
    (summable_liuSelbergAbsPrimeDeviation hNeven hN)

theorem liuAbsoluteEulerFactor_le_universal_mul_kernel
    {N : ℕ} (hNeven : Even N) (p : Nat.Primes) :
    liuAbsoluteEulerFactor N p ≤
      liuUniversalAbsEulerFactor p * liuPrimeDivisorKernel N p := by
  by_cases hpd : (p : ℕ) ∣ N
  · have hlocal : liuAbsoluteEulerFactor N p = 1 + ((p : ℝ)⁻¹) := by
      unfold liuAbsoluteEulerFactor liuSelbergAbsPrimeDeviation
      rw [tsum_abs_liuSelbergCorrection_prime_pow hNeven p.2, if_pos hpd]
      ring
    rw [hlocal, liuPrimeDivisorKernel, if_pos hpd]
    calc
      1 + ((p : ℝ)⁻¹) = 1 * (1 + ((p : ℝ)⁻¹)) := by ring
      _ ≤ liuUniversalAbsEulerFactor p * (1 + ((p : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_right
          (liuAbsoluteEulerFactor_one_le (N := 2) (by norm_num) p)
          (by positivity)
  · have hp2 : ¬(p : ℕ) ∣ 2 := by
      intro hp2
      rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with hpone | hptwo
      · exact p.2.ne_one hpone
      · apply hpd
        rw [hptwo]
        exact hNeven.two_dvd
    have hlocal : liuAbsoluteEulerFactor N p = liuUniversalAbsEulerFactor p := by
      unfold liuAbsoluteEulerFactor liuUniversalAbsEulerFactor
        liuSelbergAbsPrimeDeviation
      rw [tsum_abs_liuSelbergCorrection_prime_pow hNeven p.2, if_neg hpd,
        tsum_abs_liuSelbergCorrection_prime_pow (N := 2) (by norm_num) p.2,
        if_neg hp2]
    rw [hlocal, liuPrimeDivisorKernel, if_neg hpd, mul_one]

theorem hasProd_liuPrimeDivisorKernel
    {N : ℕ} (hN : 0 < N) :
    HasProd (liuPrimeDivisorKernel N) (liuPrimeDivisorProduct N) := by
  classical
  let e : N.primeFactors ↪ Nat.Primes :=
    ⟨fun p => ⟨p, (Nat.mem_primeFactors.mp p.2).1⟩, by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun q : Nat.Primes => (q : ℕ)) hab⟩
  let S : Finset Nat.Primes := N.primeFactors.attach.map e
  have houtside (p : Nat.Primes) (hp : p ∉ S) :
      liuPrimeDivisorKernel N p = 1 := by
    rw [liuPrimeDivisorKernel]
    apply if_neg
    intro hpd
    have hpF : (p : ℕ) ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨p.2, hpd, hN.ne'⟩
    apply hp
    dsimp only [S]
    apply Finset.mem_map.mpr
    refine ⟨⟨(p : ℕ), hpF⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl
  have hprod : (∏ p ∈ S, liuPrimeDivisorKernel N p) =
      liuPrimeDivisorProduct N := by
    unfold liuPrimeDivisorProduct
    dsimp only [S]
    rw [Finset.prod_map]
    refine Finset.prod_bij (fun p _ => (p : ℕ)) ?_ ?_ ?_ ?_
    · intro p hp
      exact p.2
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro p hp
      exact ⟨⟨p, hp⟩, by simp, rfl⟩
    · intro p hp
      have hpd : ((e p : Nat.Primes) : ℕ) ∣ N := by
        change (p : ℕ) ∣ N
        exact (Nat.mem_primeFactors.mp p.2).2.1
      rw [liuPrimeDivisorKernel, if_pos hpd]
      rfl
  rw [← hprod]
  exact hasProd_prod_of_ne_finset_one houtside

theorem tprod_universal_mul_liuPrimeDivisorKernel
    {N : ℕ} (hN : 0 < N) :
    (∏' p : Nat.Primes,
      liuUniversalAbsEulerFactor p * liuPrimeDivisorKernel N p) =
      liuUniversalAbsEuler * liuPrimeDivisorProduct N := by
  have h := multipliable_liuUniversalAbsEulerFactor.hasProd.mul
    (hasProd_liuPrimeDivisorKernel hN)
  simpa only [liuUniversalAbsEuler] using h.tprod_eq

theorem tprod_liuAbsoluteEulerFactor_le_uniform
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    (∏' p : Nat.Primes, liuAbsoluteEulerFactor N p) ≤
      liuUniversalAbsEuler * liuPrimeDivisorProduct N := by
  let h : Nat.Primes → ℝ :=
    fun p => liuUniversalAbsEulerFactor p * liuPrimeDivisorKernel N p
  have hmult : Multipliable h := by
    simpa only [h] using multipliable_liuUniversalAbsEulerFactor.mul
      (hasProd_liuPrimeDivisorKernel hN).multipliable
  have hone (p : Nat.Primes) : 1 ≤ h p := by
    dsimp only [h]
    rw [liuPrimeDivisorKernel]
    have ha : 1 ≤ liuUniversalAbsEulerFactor p :=
      liuAbsoluteEulerFactor_one_le (N := 2) (by norm_num) p
    split_ifs with hp
    · have hb : 1 ≤ 1 + ((p : ℝ)⁻¹) := by
        have hpR : 0 ≤ (p : ℝ) := by positivity
        exact le_add_of_nonneg_right (inv_nonneg.mpr hpR)
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    · nlinarith
  apply (multipliable_liuAbsoluteEulerFactor hNeven hN).tprod_le_of_prod_le
  intro s
  calc
    ∏ p ∈ s, liuAbsoluteEulerFactor N p ≤ ∏ p ∈ s, h p :=
      Finset.prod_le_prod
        (fun p _ => by linarith [liuAbsoluteEulerFactor_one_le hNeven p])
        (fun p _ => liuAbsoluteEulerFactor_le_universal_mul_kernel hNeven p)
    _ ≤ ∏' p : Nat.Primes, h p :=
      ge_of_tendsto hmult.hasProd (Filter.eventually_atTop.mpr
        ⟨s, fun t hst =>
          Finset.prod_le_prod_of_subset_of_one_le hst
            (fun p _ => by linarith [hone p])
            (fun p _ _ => hone p)⟩)
    _ = liuUniversalAbsEuler * liuPrimeDivisorProduct N := by
      exact tprod_universal_mul_liuPrimeDivisorKernel hN

theorem tsum_abs_liuSelbergCorrection_le_tprod_liuAbsoluteEulerFactor
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    (∑' d : ℕ, |liuSelbergCorrection N d|) ≤
      ∏' p : Nat.Primes, liuAbsoluteEulerFactor N p := by
  classical
  let f : ℕ → ℝ := fun d => |liuSelbergCorrection N d|
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f, liuSelbergCorrection_one]
  have hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f, (liuSelbergCorrection_isMultiplicative N).map_mul_of_coprime hmn,
      abs_mul]
  have hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => f (p ^ e)) := by
    intro p hp
    exact summable_abs_liuSelbergCorrection_prime_pow N hp
  have hmult := multipliable_liuAbsoluteEulerFactor hNeven hN
  have hrange (z : ℕ) :
      (∑ n ∈ Finset.range z, f n) ≤
        ∏' p : Nat.Primes, liuAbsoluteEulerFactor N p := by
    have hsmooth :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
        hf1 hfmul (by
          intro p hp
          apply (hlocal hp).congr
          intro e
          simp [f]) z
    have hsind : Summable (z.smoothNumbers.indicator f) :=
      summable_subtype_iff_indicator.mp (by
        change Summable (fun m : z.smoothNumbers => f m)
        simpa [f] using hsmooth.1)
    calc
      ∑ n ∈ Finset.range z, f n =
          ∑ n ∈ Finset.range z, z.smoothNumbers.indicator f n := by
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hn0 : n = 0
            · subst n
              simp [f, Set.indicator]
            · rw [Set.indicator_of_mem
                (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
                  (Finset.mem_range.mp hn))]
      _ ≤ ∑' n : ℕ, z.smoothNumbers.indicator f n :=
        hsind.sum_le_tsum _ (fun n _ => by
          by_cases hn : n ∈ z.smoothNumbers <;> simp [Set.indicator, hn, f])
      _ = ∑' n : z.smoothNumbers, f n := (_root_.tsum_subtype _ _).symm
      _ = ∏ p ∈ z.primesBelow, ∑' e : ℕ, f (p ^ e) := hsmooth.2.tsum_eq
      _ ≤ ∏' p : Nat.Primes, liuAbsoluteEulerFactor N p := by
        let e : z.primesBelow ↪ Nat.Primes :=
          ⟨fun p => ⟨p.1, Nat.prime_of_mem_primesBelow p.2⟩, by
            intro a b hab
            apply Subtype.ext
            exact congrArg (fun q : Nat.Primes => (q : ℕ)) hab⟩
        let S : Finset Nat.Primes := z.primesBelow.attach.map e
        have hprod :
            (∏ p ∈ z.primesBelow, ∑' k : ℕ, f (p ^ k)) =
              ∏ p ∈ S, liuAbsoluteEulerFactor N p := by
          refine Finset.prod_bij (fun p hp => e ⟨p, hp⟩) ?_ ?_ ?_ ?_
          · intro p hp
            simp [S]
          · intro a ha b hb hab
            exact congrArg (fun q : Nat.Primes => (q : ℕ)) hab
          · intro p hp
            dsimp only [S] at hp
            obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
            exact ⟨q.1, q.2, rfl⟩
          · intro p hp
            unfold liuAbsoluteEulerFactor liuSelbergAbsPrimeDeviation
            change (∑' k : ℕ, |liuSelbergCorrection N (p ^ k)|) =
              1 + ((∑' k : ℕ, |liuSelbergCorrection N (p ^ k)|) - 1)
            ring
        rw [hprod]
        exact ge_of_tendsto hmult.hasProd (Filter.eventually_atTop.mpr
          ⟨S, fun T hST =>
            Finset.prod_le_prod_of_subset_of_one_le hST
              (fun p _ => by
                linarith [liuAbsoluteEulerFactor_one_le hNeven p])
              (fun p _ _ => liuAbsoluteEulerFactor_one_le hNeven p)⟩)
  apply le_of_tendsto
    (summable_abs_liuSelbergCorrection hNeven hN).tendsto_sum_tsum_nat
  filter_upwards [] with z
  exact hrange z

theorem tsum_abs_liuSelbergCorrection_le_uniform
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    (∑' d : ℕ, |liuSelbergCorrection N d|) ≤
      liuUniversalAbsEuler * liuPrimeDivisorProduct N :=
  le_trans
    (tsum_abs_liuSelbergCorrection_le_tprod_liuAbsoluteEulerFactor hNeven hN)
    (tprod_liuAbsoluteEulerFactor_le_uniform hNeven hN)

theorem summable_liuUniversalAbsLogMoment :
    Summable (fun d : ℕ => |liuSelbergCorrection 2 d| * Real.log d) :=
  summable_abs_liuSelbergCorrection_mul_log_nat (by norm_num) (by norm_num)

theorem liuUniversalAbsLogMoment_nonneg : 0 ≤ liuUniversalAbsLogMoment := by
  unfold liuUniversalAbsLogMoment
  apply tsum_nonneg
  intro d
  exact mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg d)

/-- The normalized universal logarithmic moment. -/
noncomputable def liuUniversalAbsLogRatio : ℝ :=
  liuUniversalAbsLogMoment / liuUniversalAbsEuler

theorem liuUniversalAbsLogRatio_nonneg : 0 ≤ liuUniversalAbsLogRatio :=
  div_nonneg liuUniversalAbsLogMoment_nonneg liuUniversalAbsEuler_nonneg

theorem liuPrimeDivisorProduct_pos (N : ℕ) :
    0 < liuPrimeDivisorProduct N := by
  unfold liuPrimeDivisorProduct
  apply Finset.prod_pos
  intro p hp
  have hpR : 0 ≤ (p : ℝ) := by positivity
  positivity

theorem one_add_liuBaseDeviation_le_one (p : ℕ) :
    1 + liuBaseDeviation p ≤ 1 := by
  exact MathlibNt.SieveTheory.SingularSeries.one_add_liuBaseDeviation_le_one p

theorem liuUniversalProduct_le_one : liuUniversalProduct ≤ 1 := by
  unfold liuUniversalProduct
  apply Multipliable.tprod_le_of_prod_le multipliable_one_add_liuBaseDeviation
  intro s
  calc
    ∏ p ∈ s, (1 + liuBaseDeviation p) ≤ ∏ _p ∈ s, (1 : ℝ) :=
      Finset.prod_le_prod (fun p _ => (one_add_liuBaseDeviation_pos p).le)
        (fun p _ => one_add_liuBaseDeviation_le_one p)
    _ = 1 := by simp

theorem liuCorrectionFactor_le_primeCube {p : ℕ} (hp : 2 < p) :
    liuCorrectionFactor p ≤ (1 + ((p : ℝ)⁻¹)) ^ 3 := by
  unfold liuCorrectionFactor
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hpR2 : (0 : ℝ) < (p : ℝ) - 2 := by
    exact sub_pos.mpr (by exact_mod_cast hp)
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
  rw [show (1 + ((p : ℝ)⁻¹)) ^ 3 =
      ((p : ℝ) + 1) ^ 3 / (p : ℝ) ^ 3 by
        field_simp [hpne]]
  rw [div_le_div_iff₀ hpR2 (pow_pos hpR 3)]
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Nat.succ_le_iff.mpr hp)
  have hpos : 0 ≤ ((p : ℝ) - 3) * (2 * (p : ℝ) ^ 2 + 3 * (p : ℝ) + 4) :=
    mul_nonneg (sub_nonneg.mpr hp3) (by nlinarith [sq_nonneg (p : ℝ)])
  nlinarith

theorem liuCorrection_le_liuPrimeDivisorProduct_cube (N : ℕ) :
    liuCorrection N ≤ (liuPrimeDivisorProduct N) ^ 3 := by
  classical
  unfold liuCorrection
  calc
    (N.primeFactors.filter fun p => 2 < p).prod liuCorrectionFactor ≤
        (N.primeFactors.filter fun p => 2 < p).prod
          (fun p => (1 + ((p : ℝ)⁻¹)) ^ 3) :=
      Finset.prod_le_prod
        (fun p hp => (liuCorrectionFactor_pos (Finset.mem_filter.mp hp).2).le)
        (fun p hp => liuCorrectionFactor_le_primeCube
          (Finset.mem_filter.mp hp).2)
    _ ≤ N.primeFactors.prod (fun p => (1 + ((p : ℝ)⁻¹)) ^ 3) :=
      Finset.prod_le_prod_of_subset_of_one_le
        (by intro p hp; exact (Finset.mem_filter.mp hp).1)
        (fun p hp => by
          have hpR : 0 ≤ (p : ℝ) := by positivity
          have hinv : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr hpR
          positivity)
        (fun p hp hpn => by
          have hpR : 0 ≤ (p : ℝ) := by positivity
          have hinv : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr hpR
          exact one_le_pow₀ (by linarith))
    _ = (liuPrimeDivisorProduct N) ^ 3 := by
      rw [Finset.prod_pow]
      rfl

theorem liuSingularSeries_le_liuPrimeDivisorProduct_cube (N : ℕ) :
    liuSingularSeries N ≤ (liuPrimeDivisorProduct N) ^ 3 := by
  rw [liuSingularSeries]
  calc
    liuCorrection N * liuUniversalProduct ≤ liuCorrection N * 1 :=
      mul_le_mul_of_nonneg_left liuUniversalProduct_le_one (liuCorrection_pos N).le
    _ = liuCorrection N := mul_one _
    _ ≤ (liuPrimeDivisorProduct N) ^ 3 :=
      liuCorrection_le_liuPrimeDivisorProduct_cube N

/-- The logarithmic first moment of the finite prime-divisor kernel. -/
noncomputable def liuPrimeDivisorLogSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primeFactors, Real.log p / p

/-- The squarefree kernel supported on divisors of `N`.  At a prime divisor
of `N` its local coefficient is `1 / p`. -/
noncomputable def liuSquarefreeDivisorKernel (N d : ℕ) : ℝ :=
  if d ∈ N.divisors ∧ Squarefree d then (d : ℝ)⁻¹ else 0

private noncomputable def liuPrimeDivisorRadical (N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, p

private theorem liuPrimeDivisorRadical_ne_zero (N : ℕ) :
    liuPrimeDivisorRadical N ≠ 0 := by
  unfold liuPrimeDivisorRadical
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).ne_zero

private theorem liuPrimeDivisorRadical_squarefree (N : ℕ) :
    Squarefree (liuPrimeDivisorRadical N) := by
  unfold liuPrimeDivisorRadical
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq

private theorem liuSquarefreeDivisorKernel_support {N : ℕ} (hN : 0 < N) (d : ℕ) :
    (d ∈ N.divisors ∧ Squarefree d) ↔
      d ∈ (liuPrimeDivisorRadical N).divisors := by
  have hR0 := liuPrimeDivisorRadical_ne_zero N
  constructor
  · rintro ⟨hd, hdsq⟩
    rw [Nat.mem_divisors] at hd ⊢
    refine ⟨?_, hR0⟩
    rw [← Nat.prod_primeFactors_of_squarefree hdsq]
    apply (Nat.prod_primeFactors_dvd_iff hR0).mpr
    rw [show (liuPrimeDivisorRadical N).primeFactors = N.primeFactors by
      unfold liuPrimeDivisorRadical
      exact Nat.primeFactors_prod_primeFactors N]
    exact Nat.primeFactors_mono hd.1 hN.ne'
  · intro hd
    rw [Nat.mem_divisors] at hd
    refine
      ⟨Nat.mem_divisors.mpr
          ⟨hd.1.trans (Nat.prod_primeFactors_dvd N), hN.ne'⟩,
        (liuPrimeDivisorRadical_squarefree N).squarefree_of_dvd hd.1⟩

private theorem liuSquarefreeDivisorKernel_eq {N : ℕ} (hN : 0 < N) (d : ℕ) :
    liuSquarefreeDivisorKernel N d =
      if d ∈ (liuPrimeDivisorRadical N).divisors then (d : ℝ)⁻¹ else 0 := by
  unfold liuSquarefreeDivisorKernel
  by_cases hd : d ∈ (liuPrimeDivisorRadical N).divisors
  · rw [if_pos hd, if_pos ((liuSquarefreeDivisorKernel_support hN d).mpr hd)]
  · rw [if_neg hd, if_neg (mt (liuSquarefreeDivisorKernel_support hN d).mp hd)]

theorem summable_liuSquarefreeDivisorKernel {N : ℕ} (hN : 0 < N) :
    Summable (liuSquarefreeDivisorKernel N) := by
  apply summable_of_ne_finset_zero
    (s := (liuPrimeDivisorRadical N).divisors)
  intro d hd
  rw [liuSquarefreeDivisorKernel_eq hN, if_neg hd]

theorem summable_liuSquarefreeDivisorKernel_mul_log {N : ℕ} (hN : 0 < N) :
    Summable (fun d : ℕ => liuSquarefreeDivisorKernel N d * Real.log d) := by
  apply summable_of_ne_finset_zero
    (s := (liuPrimeDivisorRadical N).divisors)
  intro d hd
  rw [liuSquarefreeDivisorKernel_eq hN, if_neg hd, zero_mul]

theorem tsum_liuSquarefreeDivisorKernel {N : ℕ} (hN : 0 < N) :
    (∑' d : ℕ, liuSquarefreeDivisorKernel N d) =
      liuPrimeDivisorProduct N := by
  have hEuler :=
    liuReciprocal_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (liuPrimeDivisorRadical_squarefree N)
  rw [tsum_eq_sum (s := (liuPrimeDivisorRadical N).divisors)]
  · calc
      ∑ d ∈ (liuPrimeDivisorRadical N).divisors,
          liuSquarefreeDivisorKernel N d =
          ∑ d ∈ (liuPrimeDivisorRadical N).divisors, liuReciprocal d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [liuSquarefreeDivisorKernel_eq hN, if_pos hd]
        simp [liuReciprocal, (Nat.pos_of_mem_divisors hd).ne']
      _ = ∏ p ∈ (liuPrimeDivisorRadical N).primeFactors,
          (1 + liuReciprocal p) := hEuler.symm
      _ = liuPrimeDivisorProduct N := by
        unfold liuPrimeDivisorProduct
        rw [show (liuPrimeDivisorRadical N).primeFactors = N.primeFactors by
          unfold liuPrimeDivisorRadical
          exact Nat.primeFactors_prod_primeFactors N]
        apply Finset.prod_congr rfl
        intro p hp
        simp [liuReciprocal, (Nat.prime_of_mem_primeFactors hp).ne_zero]
  · intro d hd
    rw [liuSquarefreeDivisorKernel_eq hN, if_neg hd]

theorem liuSquarefreeDivisorKernel_nonneg (N d : ℕ) :
    0 ≤ liuSquarefreeDivisorKernel N d := by
  unfold liuSquarefreeDivisorKernel
  split_ifs
  · positivity
  · exact le_rfl

theorem liuPrimeDivisorLogSum_nonneg (N : ℕ) :
    0 ≤ liuPrimeDivisorLogSum N := by
  unfold liuPrimeDivisorLogSum
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)

theorem tsum_liuSquarefreeDivisorKernel_mul_log_le
    {N : ℕ} (hN : 0 < N) :
    (∑' d : ℕ, liuSquarefreeDivisorKernel N d * Real.log d) ≤
      liuPrimeDivisorProduct N * liuPrimeDivisorLogSum N := by
  classical
  let R := liuPrimeDivisorRadical N
  have hR0 : R ≠ 0 := liuPrimeDivisorRadical_ne_zero N
  have hRsq : Squarefree R := liuPrimeDivisorRadical_squarefree N
  have hRpf : R.primeFactors = N.primeFactors := by
    dsimp only [R]
    unfold liuPrimeDivisorRadical
    exact Nat.primeFactors_prod_primeFactors N
  rw [tsum_eq_sum (s := R.divisors)]
  · calc
      ∑ d ∈ R.divisors, liuSquarefreeDivisorKernel N d * Real.log d =
          ∑ d ∈ R.divisors, ∑ p ∈ R.primeFactors,
            if p ∣ d then
              (Real.log p / p) * liuSquarefreeDivisorKernel N (d / p)
            else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
        have hdsq : Squarefree d := hRsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
        have hdR := Nat.dvd_of_mem_divisors hd
        have hpfsub : d.primeFactors ⊆ R.primeFactors :=
          Nat.primeFactors_mono hdR hR0
        rw [liuSquarefreeDivisorKernel_eq hN, if_pos hd]
        rw [Real.log_nat_eq_sum_factorization]
        rw [Finsupp.sum, Nat.support_factorization, Finset.mul_sum]
        calc
          ∑ p ∈ d.primeFactors,
              (d : ℝ)⁻¹ * ((d.factorization p : ℝ) * Real.log p) =
              ∑ p ∈ d.primeFactors, (Real.log p / p) *
                liuSquarefreeDivisorKernel N (d / p) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
            have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
            have hpdR : d / p ∣ R :=
              (Nat.div_dvd_of_dvd hpd).trans hdR
            have hdpmem : d / p ∈ R.divisors :=
              Nat.mem_divisors.mpr ⟨hpdR, hR0⟩
            rw [liuSquarefreeDivisorKernel_eq hN, if_pos hdpmem]
            have hfac : d.factorization p = 1 :=
              Nat.factorization_eq_one_of_squarefree hdsq hpprime hpd
            rw [hfac, Nat.cast_one, one_mul]
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
            have hdp0 : ((d / p : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.div_pos
                (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hpd) hpprime.pos).ne'
            have hdpcast : (d : ℝ) = (p : ℝ) * (d / p : ℕ) := by
              exact_mod_cast (Nat.mul_div_cancel' hpd).symm
            rw [hdpcast]
            field_simp [hp0, hdp0]
          _ = ∑ p ∈ R.primeFactors,
              if p ∣ d then (Real.log p / p) *
                liuSquarefreeDivisorKernel N (d / p) else 0 := by
            calc
              ∑ p ∈ d.primeFactors, (Real.log p / p) *
                    liuSquarefreeDivisorKernel N (d / p) =
                  ∑ p ∈ d.primeFactors, if p ∣ d then (Real.log p / p) *
                    liuSquarefreeDivisorKernel N (d / p) else 0 := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [if_pos (Nat.dvd_of_mem_primeFactors hp)]
              _ = _ := Finset.sum_subset hpfsub (by
                intro p hpR hp
                rw [if_neg]
                intro hpd
                exact hp (Nat.mem_primeFactors.mpr
                  ⟨Nat.prime_of_mem_primeFactors hpR, hpd, hd0⟩))
      _ ≤ ∑ p ∈ N.primeFactors, (Real.log p / p) *
          ∑' e : ℕ, liuSquarefreeDivisorKernel N e := by
        rw [Finset.sum_comm]
        rw [← hRpf]
        apply Finset.sum_le_sum
        intro p hp
        have hpprime := Nat.prime_of_mem_primeFactors hp
        rw [← Finset.sum_filter, ← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left
        · let A := R.divisors.filter (fun d => p ∣ d)
          have hinj : Set.InjOn (fun d : ℕ => d / p) ↑A := by
            intro a ha b hb hab
            have hpa : p ∣ a := (Finset.mem_filter.mp ha).2
            have hpb : p ∣ b := (Finset.mem_filter.mp hb).2
            calc
              a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
              _ = p * (b / p) := congrArg (fun e => p * e) hab
              _ = b := Nat.mul_div_cancel' hpb
          rw [← Finset.sum_image hinj]
          exact (summable_liuSquarefreeDivisorKernel hN).sum_le_tsum _
            (fun e _ => liuSquarefreeDivisorKernel_nonneg N e)
        · exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
      _ = liuPrimeDivisorProduct N * liuPrimeDivisorLogSum N := by
        rw [tsum_liuSquarefreeDivisorKernel hN]
        unfold liuPrimeDivisorLogSum
        rw [← Finset.sum_mul]
        ring
  · intro d hd
    rw [liuSquarefreeDivisorKernel_eq hN, if_neg hd, zero_mul]

/-- The absolute Selberg correction as an arithmetic function. -/
noncomputable def liuSelbergCorrectionAbsFunction (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => |liuSelbergCorrection N n|, by simp⟩

@[simp]
theorem liuSelbergCorrectionAbsFunction_apply (N n : ℕ) :
    liuSelbergCorrectionAbsFunction N n = |liuSelbergCorrection N n| := rfl

theorem liuSelbergCorrectionAbsFunction_isMultiplicative (N : ℕ) :
    (liuSelbergCorrectionAbsFunction N).IsMultiplicative := by
  refine ⟨by simp [liuSelbergCorrectionAbsFunction, liuSelbergCorrection_one], ?_⟩
  intro m n hmn
  simp [liuSelbergCorrectionAbsFunction,
    (liuSelbergCorrection_isMultiplicative N).map_mul_of_coprime hmn, abs_mul]

theorem tsum_abs_liuSelbergCorrection_two_eq_liuUniversalAbsEuler :
    (∑' d : ℕ, |liuSelbergCorrection 2 d|) = liuUniversalAbsEuler := by
  have hsum : Summable (fun d : ℕ =>
      ‖liuSelbergCorrectionAbsFunction 2 d‖) := by
    simpa [liuSelbergCorrectionAbsFunction_apply] using
      (summable_abs_liuSelbergCorrection (N := 2) (by norm_num) (by norm_num)).norm
  have hEuler :=
    (liuSelbergCorrectionAbsFunction_isMultiplicative 2).eulerProduct_tprod hsum
  change (∑' d : ℕ, liuSelbergCorrectionAbsFunction 2 d) =
    liuUniversalAbsEuler
  rw [← hEuler]
  unfold liuUniversalAbsEuler liuUniversalAbsEulerFactor
    liuSelbergAbsPrimeDeviation
  apply tprod_congr
  intro p
  simp only [liuSelbergCorrectionAbsFunction_apply]
  ring

/-- The finite squarefree divisor kernel as an arithmetic function. -/
noncomputable def liuSquarefreeDivisorKernelFunction (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨liuSquarefreeDivisorKernel N, by simp [liuSquarefreeDivisorKernel]⟩

@[simp]
theorem liuSquarefreeDivisorKernelFunction_apply (N n : ℕ) :
    liuSquarefreeDivisorKernelFunction N n = liuSquarefreeDivisorKernel N n := rfl

theorem liuSquarefreeDivisorKernelFunction_isMultiplicative
    {N : ℕ} (hN : 0 < N) :
    (liuSquarefreeDivisorKernelFunction N).IsMultiplicative := by
  classical
  refine ⟨by simp [liuSquarefreeDivisorKernelFunction, liuSquarefreeDivisorKernel,
    Nat.one_mem_divisors.mpr hN.ne'], ?_⟩
  intro m n hmn
  simp only [liuSquarefreeDivisorKernelFunction_apply]
  unfold liuSquarefreeDivisorKernel
  have hdiv : m * n ∣ N ↔ m ∣ N ∧ n ∣ N := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right m n).trans h, (dvd_mul_left n m).trans h⟩
    · rintro ⟨hm, hn⟩
      exact (Nat.coprime_iff_isRelPrime.mp hmn).mul_dvd hm hn
  have hmem : m * n ∈ N.divisors ↔ m ∈ N.divisors ∧ n ∈ N.divisors := by
    simp only [Nat.mem_divisors, hdiv]
    tauto
  have hsq := Nat.squarefree_mul hmn
  by_cases hm : m ∈ N.divisors ∧ Squarefree m <;>
    by_cases hn : n ∈ N.divisors ∧ Squarefree n
  · rw [if_pos ⟨hmem.mpr ⟨hm.1, hn.1⟩, hsq.mpr ⟨hm.2, hn.2⟩⟩,
      if_pos hm, if_pos hn,
      Nat.cast_mul, mul_inv]
  · rw [if_neg, if_pos hm, if_neg hn, mul_zero]
    intro h
    exact hn ⟨(hmem.mp h.1).2, (hsq.mp h.2).2⟩
  · rw [if_neg, if_neg hm, if_pos hn, zero_mul]
    intro h
    exact hm ⟨(hmem.mp h.1).1, (hsq.mp h.2).1⟩
  · rw [if_neg, if_neg hm, if_neg hn, zero_mul]
    intro h
    exact hm ⟨(hmem.mp h.1).1, (hsq.mp h.2).1⟩

/-- The universal absolute correction convolved with the finite divisor kernel. -/
noncomputable def liuSelbergAbsKernelConvolution (N : ℕ) : ArithmeticFunction ℝ :=
  liuSelbergCorrectionAbsFunction 2 * liuSquarefreeDivisorKernelFunction N

theorem liuSelbergAbsKernelConvolution_isMultiplicative
    {N : ℕ} (hN : 0 < N) :
    (liuSelbergAbsKernelConvolution N).IsMultiplicative :=
  (liuSelbergCorrectionAbsFunction_isMultiplicative 2).mul
    (liuSquarefreeDivisorKernelFunction_isMultiplicative hN)

theorem liuSelbergAbsKernelConvolution_nonneg (N n : ℕ) :
    0 ≤ liuSelbergAbsKernelConvolution N n := by
  rw [liuSelbergAbsKernelConvolution, ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (abs_nonneg _)
    (liuSquarefreeDivisorKernel_nonneg N _)

theorem liuSelbergCorrectionAbsFunction_two_le_convolution
    {N n : ℕ} (hN : 0 < N) :
    liuSelbergCorrectionAbsFunction 2 n ≤ liuSelbergAbsKernelConvolution N n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [liuSelbergAbsKernelConvolution, ArithmeticFunction.mul_apply]
  have hmem : (n, 1) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩
  calc
    liuSelbergCorrectionAbsFunction 2 n =
        liuSelbergCorrectionAbsFunction 2 n *
          liuSquarefreeDivisorKernelFunction N 1 := by
      simp [liuSquarefreeDivisorKernel, Nat.one_mem_divisors.mpr hN.ne']
    _ ≤ ∑ d ∈ n.divisorsAntidiagonal,
          liuSelbergCorrectionAbsFunction 2 d.1 *
            liuSquarefreeDivisorKernelFunction N d.2 := by
      exact Finset.single_le_sum
        (f := fun d : ℕ × ℕ => liuSelbergCorrectionAbsFunction 2 d.1 *
          liuSquarefreeDivisorKernelFunction N d.2)
        (fun d hd => mul_nonneg (abs_nonneg _)
          (liuSquarefreeDivisorKernel_nonneg N _)) hmem

theorem liuSquarefreeDivisorKernelFunction_le_convolution
    {N n : ℕ} (_hN : 0 < N) :
    liuSquarefreeDivisorKernelFunction N n ≤ liuSelbergAbsKernelConvolution N n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [liuSelbergAbsKernelConvolution, ArithmeticFunction.mul_apply]
  have hmem : (1, n) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩
  calc
    liuSquarefreeDivisorKernelFunction N n =
        liuSelbergCorrectionAbsFunction 2 1 *
          liuSquarefreeDivisorKernelFunction N n := by
      simp [liuSelbergCorrection_one]
    _ ≤ ∑ d ∈ n.divisorsAntidiagonal,
          liuSelbergCorrectionAbsFunction 2 d.1 *
            liuSquarefreeDivisorKernelFunction N d.2 := by
      exact Finset.single_le_sum
        (f := fun d : ℕ × ℕ => liuSelbergCorrectionAbsFunction 2 d.1 *
          liuSquarefreeDivisorKernelFunction N d.2)
        (fun d hd => mul_nonneg (abs_nonneg _)
          (liuSquarefreeDivisorKernel_nonneg N _)) hmem

theorem abs_liuSelbergCorrection_prime_pow_eq_two_of_not_dvd
    {N p e : ℕ} (hNeven : Even N) (hp : p.Prime) (hpn : ¬p ∣ N) :
    |liuSelbergCorrection N (p ^ e)| = |liuSelbergCorrection 2 (p ^ e)| := by
  have hp2 : ¬p ∣ 2 := by
    intro hpd
    rcases (Nat.dvd_prime Nat.prime_two).mp hpd with hpone | hptwo
    · exact hp.ne_one hpone
    · exact hpn (hptwo ▸ hNeven.two_dvd)
  cases e with
  | zero => simp [liuSelbergCorrection_one]
  | succ e =>
      cases e with
      | zero =>
          simp only [Nat.zero_add, pow_one]
          rw [liuSelbergCorrection_prime_of_not_dvd hNeven hp hpn,
            liuSelbergCorrection_prime_of_not_dvd (N := 2) (by norm_num) hp hp2]
      | succ e =>
          cases e with
          | zero =>
              change |liuSelbergCorrection N (p ^ 2)| =
                |liuSelbergCorrection 2 (p ^ 2)|
              rw [liuSelbergCorrection_prime_sq_of_not_dvd hp hpn,
                liuSelbergCorrection_prime_sq_of_not_dvd hp hp2]
          | succ e =>
              rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpn (by omega),
                liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hp2 (by omega)]

theorem liuSelbergCorrectionAbsFunction_prime_pow_le_convolution
    {N p e : ℕ} (hNeven : Even N) (hN : 0 < N) (hp : p.Prime) :
    liuSelbergCorrectionAbsFunction N (p ^ e) ≤
      liuSelbergAbsKernelConvolution N (p ^ e) := by
  by_cases hpn : p ∣ N
  · cases e with
    | zero =>
        simpa [liuSelbergCorrectionAbsFunction, liuSelbergCorrection_one] using
          (liuSelbergCorrectionAbsFunction_two_le_convolution
            (N := N) (n := 1) hN)
    | succ e =>
        cases e with
        | zero =>
            have hk := liuSquarefreeDivisorKernelFunction_le_convolution
              (N := N) (n := p) hN
            rw [liuSelbergCorrectionAbsFunction_apply, Nat.pow_one,
              liuSelbergCorrection_prime_of_dvd hp hpn]
            simpa [liuSquarefreeDivisorKernelFunction, liuSquarefreeDivisorKernel,
              Nat.mem_divisors.mpr ⟨hpn, hN.ne'⟩, hp.squarefree] using hk
        | succ e =>
            rw [liuSelbergCorrectionAbsFunction_apply,
              liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpn (by omega),
              abs_zero]
            exact liuSelbergAbsKernelConvolution_nonneg N _
  · rw [liuSelbergCorrectionAbsFunction_apply,
      abs_liuSelbergCorrection_prime_pow_eq_two_of_not_dvd hNeven hp hpn,
      ← liuSelbergCorrectionAbsFunction_apply]
    exact liuSelbergCorrectionAbsFunction_two_le_convolution hN

theorem liuSelbergCorrectionAbsFunction_le_convolution
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) (n : ℕ) :
    liuSelbergCorrectionAbsFunction N n ≤ liuSelbergAbsKernelConvolution N n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (liuSelbergCorrectionAbsFunction N)
      (liuSelbergCorrectionAbsFunction_isMultiplicative N) hn,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (liuSelbergAbsKernelConvolution N)
      (liuSelbergAbsKernelConvolution_isMultiplicative hN) hn,
    Nat.prod_factorization_eq_prod_primeFactors,
    Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_le_prod
  · intro p hpN
    exact abs_nonneg _
  intro p hpN
  exact liuSelbergCorrectionAbsFunction_prime_pow_le_convolution hNeven hN
    (Nat.prime_of_mem_primeFactors hpN)

set_option maxHeartbeats 1800000 in
private theorem tsum_arithmeticFunction_convolution_mul_log
    (f g : ArithmeticFunction ℝ)
    (hf : Summable fun n : ℕ => ‖f n‖)
    (hfl : Summable fun n : ℕ => ‖f n * Real.log n‖)
    (hg : Summable fun n : ℕ => ‖g n‖)
    (hgl : Summable fun n : ℕ => ‖g n * Real.log n‖) :
    Summable (fun n : ℕ => (f * g) n * Real.log n) ∧
      (∑' n : ℕ, (f * g) n * Real.log n) =
        (∑' n : ℕ, f n * Real.log n) * (∑' n : ℕ, g n) +
          (∑' n : ℕ, f n) * (∑' n : ℕ, g n * Real.log n) := by
  let F : ℕ+ × ℕ+ → ℝ := fun z =>
    (f z.1 * Real.log z.1) * g z.2 + f z.1 * (g z.2 * Real.log z.2)
  have hfp : Summable fun n : ℕ+ => ‖f n‖ :=
    hf.comp_injective PNat.coe_injective
  have hflp : Summable fun n : ℕ+ => ‖f n * Real.log n‖ :=
    hfl.comp_injective PNat.coe_injective
  have hgp : Summable fun n : ℕ+ => ‖g n‖ :=
    hg.comp_injective PNat.coe_injective
  have hglp : Summable fun n : ℕ+ => ‖g n * Real.log n‖ :=
    hgl.comp_injective PNat.coe_injective
  have hF1 : Summable fun z : ℕ+ × ℕ+ =>
      (f z.1 * Real.log z.1) * g z.2 :=
    summable_mul_of_summable_norm hflp hgp
  have hF2 : Summable fun z : ℕ+ × ℕ+ =>
      f z.1 * (g z.2 * Real.log z.2) :=
    summable_mul_of_summable_norm hfp hglp
  have hF : Summable F := hF1.add hF2
  have hSigma : Summable (F ∘ sigmaAntidiagonalEquivProd) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hF
  have hfiber (n : ℕ+) :
      (∑' c : (n : ℕ).divisorsAntidiagonal,
        (F ∘ sigmaAntidiagonalEquivProd) ⟨n, c⟩) =
        (f * g) n * Real.log n := by
    rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
    simp only [tsum_fintype, Finset.univ_eq_attach, F, Function.comp_apply,
      sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
      Equiv.coe_fn_mk]
    refine Finset.sum_bij (fun c _ => (c : ℕ × ℕ)) ?_ ?_ ?_ ?_
    · intro c hc
      exact c.2
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro b hb
      exact ⟨⟨b, hb⟩, by simp, rfl⟩
    · intro c hc
      have hc0 : (c.1.1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.pos_of_mem_divisors
          (Nat.fst_mem_divisors_of_mem_antidiagonal c.2)).ne'
      have hc1 : (c.1.2 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.pos_of_mem_divisors
          (Nat.snd_mem_divisors_of_mem_antidiagonal c.2)).ne'
      have hmul : c.1.1 * c.1.2 = n :=
        (Nat.mem_divisorsAntidiagonal.mp c.2).1
      have hcast : (c.1.1 : ℝ) * c.1.2 = (n : ℝ) := by
        exact_mod_cast hmul
      have hlog : Real.log (n : ℝ) =
          Real.log c.1.1 + Real.log c.1.2 := by
        rw [← hcast, Real.log_mul hc0 hc1]
      rw [hlog]
      ring
  have hPnat : Summable (fun n : ℕ+ => (f * g) n * Real.log n) :=
    hSigma.sigma.congr hfiber
  have hNat : Summable (fun n : ℕ => (f * g) n * Real.log n) := by
    rw [← summable_nat_add_iff 1]
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => (f * g) n * Real.log n)).mp hPnat
  refine ⟨hNat, ?_⟩
  have hf' := hf.of_norm
  have hfl' := hfl.of_norm
  have hg' := hg.of_norm
  have hgl' := hgl.of_norm
  have hfp_tsum : (∑' n : ℕ+, f n) = ∑' n : ℕ, f n := by
    simpa using tsum_zero_pnat_eq_tsum_nat hf'
  have hflp_tsum : (∑' n : ℕ+, f n * Real.log n) =
      ∑' n : ℕ, f n * Real.log n := by
    simpa using tsum_zero_pnat_eq_tsum_nat hfl'
  have hgp_tsum : (∑' n : ℕ+, g n) = ∑' n : ℕ, g n := by
    simpa using tsum_zero_pnat_eq_tsum_nat hg'
  have hglp_tsum : (∑' n : ℕ+, g n * Real.log n) =
      ∑' n : ℕ, g n * Real.log n := by
    simpa using tsum_zero_pnat_eq_tsum_nat hgl'
  calc
    (∑' n : ℕ, (f * g) n * Real.log n) =
        ∑' n : ℕ+, (f * g) n * Real.log n := by
      simpa using (tsum_zero_pnat_eq_tsum_nat hNat).symm
    _ = ∑' c : (n : ℕ+) × (n : ℕ).divisorsAntidiagonal,
          (F ∘ sigmaAntidiagonalEquivProd) c := by
      rw [hSigma.tsum_sigma]
      exact tsum_congr fun n => (hfiber n).symm
    _ = ∑' z : ℕ+ × ℕ+, F z := sigmaAntidiagonalEquivProd.tsum_eq F
    _ = (∑' z : ℕ+ × ℕ+, (f z.1 * Real.log z.1) * g z.2) +
          ∑' z : ℕ+ × ℕ+, f z.1 * (g z.2 * Real.log z.2) := by
      simpa [F] using hF1.tsum_add hF2
    _ = (∑' n : ℕ+, f n * Real.log n) * (∑' n : ℕ+, g n) +
          (∑' n : ℕ+, f n) * (∑' n : ℕ+, g n * Real.log n) := by
      rw [tsum_mul_tsum_of_summable_norm hflp hgp,
        tsum_mul_tsum_of_summable_norm hfp hglp]
    _ = _ := by rw [hflp_tsum, hgp_tsum, hfp_tsum, hglp_tsum]

/-- The nonnegative logarithmic moment in the exact denominator correction. -/
noncomputable def liuSelbergAbsoluteLogMoment (N : ℕ) : ℝ :=
  ∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d

/-- The nonnegative absolute mass in the exact denominator correction. -/
noncomputable def liuSelbergAbsoluteMass (N : ℕ) : ℝ :=
  ∑' d : ℕ, |liuSelbergCorrection N d|

theorem tsum_liuSelbergAbsKernelConvolution_mul_log
    {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, liuSelbergAbsKernelConvolution N n * Real.log n) =
      liuUniversalAbsLogMoment * liuPrimeDivisorProduct N +
        (∑' n : ℕ, |liuSelbergCorrection 2 n|) *
          (∑' n : ℕ, liuSquarefreeDivisorKernel N n * Real.log n) := by
  have hf : Summable fun n : ℕ =>
      ‖liuSelbergCorrectionAbsFunction 2 n‖ := by
    simpa [liuSelbergCorrectionAbsFunction_apply] using
      (summable_abs_liuSelbergCorrection (N := 2) (by norm_num) (by norm_num)).norm
  have hfl : Summable fun n : ℕ =>
      ‖liuSelbergCorrectionAbsFunction 2 n * Real.log n‖ := by
    simpa [liuSelbergCorrectionAbsFunction_apply] using
      summable_liuUniversalAbsLogMoment.norm
  have hg : Summable fun n : ℕ =>
      ‖liuSquarefreeDivisorKernelFunction N n‖ := by
    simpa [liuSquarefreeDivisorKernelFunction_apply] using
      (summable_liuSquarefreeDivisorKernel hN).norm
  have hgl : Summable fun n : ℕ =>
      ‖liuSquarefreeDivisorKernelFunction N n * Real.log n‖ := by
    simpa [liuSquarefreeDivisorKernelFunction_apply] using
      (summable_liuSquarefreeDivisorKernel_mul_log hN).norm
  simpa [liuSelbergAbsKernelConvolution, liuUniversalAbsLogMoment,
    liuSelbergCorrectionAbsFunction_apply, liuSquarefreeDivisorKernelFunction_apply,
    tsum_liuSquarefreeDivisorKernel hN] using
      (tsum_arithmeticFunction_convolution_mul_log
        (liuSelbergCorrectionAbsFunction 2)
        (liuSquarefreeDivisorKernelFunction N) hf hfl hg hgl).2

theorem liuSelbergAbsoluteLogMoment_le_uniform
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    liuSelbergAbsoluteLogMoment N ≤
      liuPrimeDivisorProduct N *
        (liuUniversalAbsLogMoment +
          liuUniversalAbsEuler * liuPrimeDivisorLogSum N) := by
  have hconvSummable : Summable (fun n : ℕ =>
      liuSelbergAbsKernelConvolution N n * Real.log n) := by
    have hf : Summable fun n : ℕ =>
        ‖liuSelbergCorrectionAbsFunction 2 n‖ := by
      simpa [liuSelbergCorrectionAbsFunction_apply] using
        (summable_abs_liuSelbergCorrection (N := 2) (by norm_num) (by norm_num)).norm
    have hfl : Summable fun n : ℕ =>
        ‖liuSelbergCorrectionAbsFunction 2 n * Real.log n‖ := by
      simpa [liuSelbergCorrectionAbsFunction_apply] using
        summable_liuUniversalAbsLogMoment.norm
    have hg : Summable fun n : ℕ =>
        ‖liuSquarefreeDivisorKernelFunction N n‖ := by
      simpa [liuSquarefreeDivisorKernelFunction_apply] using
        (summable_liuSquarefreeDivisorKernel hN).norm
    have hgl : Summable fun n : ℕ =>
        ‖liuSquarefreeDivisorKernelFunction N n * Real.log n‖ := by
      simpa [liuSquarefreeDivisorKernelFunction_apply] using
        (summable_liuSquarefreeDivisorKernel_mul_log hN).norm
    exact (tsum_arithmeticFunction_convolution_mul_log
      (liuSelbergCorrectionAbsFunction 2)
      (liuSquarefreeDivisorKernelFunction N) hf hfl hg hgl).1
  unfold liuSelbergAbsoluteLogMoment
  calc
    (∑' n : ℕ, |liuSelbergCorrection N n| * Real.log n) ≤
        ∑' n : ℕ, liuSelbergAbsKernelConvolution N n * Real.log n := by
      apply Summable.tsum_le_tsum
      · intro n
        exact mul_le_mul_of_nonneg_right
          (liuSelbergCorrectionAbsFunction_le_convolution hNeven hN n)
          (Real.log_natCast_nonneg n)
      · exact summable_abs_liuSelbergCorrection_mul_log_nat hNeven hN
      · exact hconvSummable
    _ = liuUniversalAbsLogMoment * liuPrimeDivisorProduct N +
          (∑' n : ℕ, |liuSelbergCorrection 2 n|) *
            (∑' n : ℕ, liuSquarefreeDivisorKernel N n * Real.log n) :=
      tsum_liuSelbergAbsKernelConvolution_mul_log hN
    _ ≤ liuUniversalAbsLogMoment * liuPrimeDivisorProduct N +
          liuUniversalAbsEuler *
            (liuPrimeDivisorProduct N * liuPrimeDivisorLogSum N) := by
      rw [tsum_abs_liuSelbergCorrection_two_eq_liuUniversalAbsEuler]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (tsum_liuSquarefreeDivisorKernel_mul_log_le hN)
          liuUniversalAbsEuler_nonneg)
    _ = liuPrimeDivisorProduct N *
        (liuUniversalAbsLogMoment +
          liuUniversalAbsEuler * liuPrimeDivisorLogSum N) := by ring

theorem liuSelbergAbsoluteLogMoment_le_uniform_normalized
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    liuSelbergAbsoluteLogMoment N ≤
      liuUniversalAbsEuler * liuPrimeDivisorProduct N *
        (liuUniversalAbsLogRatio + liuPrimeDivisorLogSum N) := by
  rw [liuUniversalAbsLogRatio]
  field_simp [liuUniversalAbsEuler_ne_zero]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    liuSelbergAbsoluteLogMoment_le_uniform hNeven hN

theorem liuSelbergCorrectionAbsTail_markov
    {N x : ℕ} (hNeven : Even N) (hN : 0 < N) (hx : 2 ≤ x) :
    Real.log x * (∑' d : ℕ, liuSelbergCorrectionAbsTail N x d) ≤
      liuSelbergAbsoluteLogMoment N := by
  rw [← tsum_mul_left]
  unfold liuSelbergAbsoluteLogMoment
  apply Summable.tsum_le_tsum
  · intro d
    by_cases hxd : x < d
    · have hxR : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hx)
      have hdR : (0 : ℝ) < d := by
        exact_mod_cast (lt_trans (lt_of_lt_of_le (by norm_num) hx) hxd)
      have hlog : Real.log (x : ℝ) ≤ Real.log (d : ℝ) :=
        Real.strictMonoOn_log.monotoneOn hxR hdR (by exact_mod_cast hxd.le)
      have hm : d ∈ {d : ℕ | x < d} := hxd
      rw [liuSelbergCorrectionAbsTail, Set.indicator_of_mem hm]
      calc
        Real.log (x : ℝ) * |liuSelbergCorrection N d| =
            |liuSelbergCorrection N d| * Real.log (x : ℝ) := mul_comm _ _
        _ ≤ |liuSelbergCorrection N d| * Real.log (d : ℝ) :=
          mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    · have hnot : d ∉ {d : ℕ | x < d} := by simpa using hxd
      rw [liuSelbergCorrectionAbsTail, Set.indicator_of_notMem hnot, mul_zero]
      exact mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg d)
  · exact (summable_liuSelbergCorrectionAbsTail hNeven hN).mul_left _
  · exact summable_abs_liuSelbergCorrection_mul_log_nat hNeven hN

theorem abs_liuSelbergArithmetic_sum_Icc_sub_log_main_le_uniform_reduction
    {N x : ℕ} (hNeven : Even N) (hN : 0 < N) (hx : 2 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 x, liuSelbergArithmetic N n) -
        Real.log x / (2 * liuSingularSeries N)| ≤
      2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N := by
  rw [liuSelbergAbsoluteLogMoment, liuSelbergAbsoluteMass]
  have hfixed := abs_liuSelbergArithmetic_sum_Icc_sub_log_main_le
    (N := N) (x := x) hNeven hN (by omega)
  calc
    |(∑ n ∈ Finset.Icc 1 x, liuSelbergArithmetic N n) -
        Real.log x / (2 * liuSingularSeries N)| ≤
        Real.log x * (∑' d : ℕ, liuSelbergCorrectionAbsTail N x d) +
          (∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d) +
          ∑' d : ℕ, |liuSelbergCorrection N d| := hfixed
    _ ≤ (∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d) +
          (∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d) +
          ∑' d : ℕ, |liuSelbergCorrection N d| := by
      gcongr
      exact liuSelbergCorrectionAbsTail_markov hNeven hN hx
    _ = 2 * (∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d) +
          ∑' d : ℕ, |liuSelbergCorrection N d| := by ring

end MathlibNt.SieveTheory.LiuWeight
