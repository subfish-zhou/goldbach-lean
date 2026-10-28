import MathlibNt.SieveTheory.Switching.RosserSieveAsymptotics

/-!
# Varying-prime asymptotics and q¹ penalty distribution

Upper Rosser density and weighted distribution inputs control varying-prime
asymptotics. Negligible proper powers reduce the full penalty to q¹ counts;
double Möbius identities retain the separate, explicit aggregate-error hypotheses.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- Conditioning by `q` changes only the carrier and total mass, not the
sifting product or its local density. -/
theorem jurkatRichertSourceConditioned_dimensionOneLocalProductBound
    {N q : ℕ} {K : ℝ}
    (h : HasDimensionOneLocalProductBound
      (jurkatRichertSourceBoundingSieve N) K) :
    HasDimensionOneLocalProductBound
      (jurkatRichertSourceConditionedBoundingSieve N q) K := by
  simpa [HasDimensionOneLocalProductBound,
    jurkatRichertSourceBoundingSieve,
    jurkatRichertSourceConditionedBoundingSieve] using h

/-- Every prime in a conditioned source sieve lies below the literal real
sifting cutoff `N^(1/10)`. -/
theorem jurkatRichertSourceConditioned_primeFactor_le_cutoff
    (N q : ℕ) :
    ∀ p ∈ (jurkatRichertSourceConditionedBoundingSieve N q).prodPrimes.primeFactors,
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ jurkatRichertSourceSiftingProduct N :=
    (Nat.mem_primeFactors_of_ne_zero
      (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp |>.2
  exact
    (prime_dvd_jurkatRichertSourceSiftingProduct hpPrime).mp hpDvd |>.2.1

/-- For the epsilon range produced by prime-q partial summation, every medium-q
upper-sieve ratio lies in the generic fundamental lemma's interval. -/
theorem jurkatRichertSourceUpperSieveRatio_mem
    {N q : ℕ} {ε : ℝ} (hN : 1 < N) (hε : 0 < ε) (hεSmall : ε < 1 / 60)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    jurkatRichertSourceUpperSieveRatio N q ε ∈
      Set.Icc (3 / 2 : ℝ) 4 := by
  have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2.1
  have hlog := jurkatRichertSourceMediumPrime_log_mem hN hq
  rcases hlog with ⟨hlogLower, hlogUpper⟩
  rw [jurkatRichertSourceUpperSieveRatio_eq_zero_sub hN hqPrime.pos,
    jurkatRichertSourceUpperSieveRatio_zero hN hqPrime.pos]
  constructor <;> linarith

/-- The shifted reciprocal mass of Chen's medium primes is uniformly bounded.
The underlying unshifted sum converges to `log ((1/3)/(1/10))`; the factor two
only replaces `1/q` by `1/(q-1)`. -/
private theorem eventually_jurkatRichertSource_shiftedPrimeReciprocalSum_le :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∑ q ∈ jurkatRichertSourceMediumPrimes N, 1 / ((q : ℝ) - 1) ≤
        2 * (Real.log ((1 / 3 : ℝ) / (1 / 10 : ℝ)) + 1) := by
  have hlimit :=
    MertensTheorem.tendsto_weightedPrimeReciprocalLogSum_const
      (a := (1 / 10 : ℝ)) (b := (1 / 3 : ℝ)) (c := (1 : ℝ))
      (by norm_num) (by norm_num)
  have hupper :
      ∀ᶠ N : ℕ in Filter.atTop,
        MertensTheorem.weightedPrimeReciprocalLogSum
            (fun _ => (1 : ℝ)) N (1 / 10) (1 / 3) ≤
          Real.log ((1 / 3 : ℝ) / (1 / 10 : ℝ)) + 1 :=
    hlimit.eventually (Iic_mem_nhds (by linarith))
  filter_upwards [hupper, Filter.eventually_ge_atTop 2] with N hupperN hN
  rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor (by omega : 1 ≤ N)]
  calc
    ∑ q ∈ (Finset.Ioc
          (MertensTheorem.rpowFloor N (1 / 10 : ℝ))
          (MertensTheorem.rpowFloor N (1 / 3 : ℝ))).filter Nat.Prime,
        1 / ((q : ℝ) - 1) ≤
        ∑ q ∈ (Finset.Ioc
          (MertensTheorem.rpowFloor N (1 / 10 : ℝ))
          (MertensTheorem.rpowFloor N (1 / 3 : ℝ))).filter Nat.Prime,
          2 * (1 / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2
      have hqr : 0 < (q : ℝ) := by exact_mod_cast hqPrime.pos
      have hqSub : 0 < (q : ℝ) - 1 := by
        have hqOne : (1 : ℝ) < q := by exact_mod_cast hqPrime.one_lt
        linarith
      rw [div_le_iff₀ hqSub]
      have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hqPrime.two_le
      field_simp [hqr.ne']
      nlinarith
    _ = 2 * MertensTheorem.weightedPrimeReciprocalLogSum
          (fun _ => (1 : ℝ)) N (1 / 10) (1 / 3) := by
      unfold MertensTheorem.weightedPrimeReciprocalLogSum
      rw [Finset.mul_sum]
    _ ≤ 2 * (Real.log ((1 / 3 : ℝ) / (1 / 10 : ℝ)) + 1) :=
      mul_le_mul_of_nonneg_left hupperN (by norm_num)

private theorem eventually_jurkatRichertSource_shiftedPrimeSum_upper
    (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 60 ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∑ q ∈ jurkatRichertSourceMediumPrimes N,
            jurkatRichertUpperLinearSieveFactor
                (jurkatRichertSourceUpperSieveRatio N q ε) /
              ((q : ℝ) - 1) ≤
          2 * Real.exp Real.eulerMascheroniConstant / 5 *
              (Real.log 8 + jurkatRichertK / 2) +
            η := by
  let f : ℝ → ℝ :=
    fun a => jurkatRichertUpperLinearSieveFactor (5 - 10 * a)
  let J : ℝ :=
    2 * Real.exp Real.eulerMascheroniConstant / 5 *
      (Real.log 8 + jurkatRichertK / 2)
  have hIntegral : (∫ a in (1 / 10 : ℝ)..(1 / 3 : ℝ), f a / a) = J := by
    simpa [f, J] using jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  have hJ : 0 ≤ J := by
    rw [← hIntegral]
    apply intervalIntegral.integral_nonneg
    · norm_num
    · intro a ha
      exact div_nonneg
        (jurkatRichertUpperLinearSieveFactor_zeroEpsilon_nonneg ha)
        (by
          have := ha.1
          norm_num at this ⊢
          linarith)
  let d : ℝ := min 1 (η / (3 * J + 4))
  have hden : 0 < 3 * J + 4 := by linarith
  have hd : 0 < d := lt_min (by norm_num) (div_pos hη hden)
  have hd_one : d ≤ 1 := min_le_left _ _
  have hd_η : d * (3 * J + 4) ≤ η :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hd_sq : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd_one)]
  have hd_cube : d ^ 3 ≤ d := by
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd_sq)]
  have hd_sq_J : d ^ 2 * J ≤ d * J :=
    mul_le_mul_of_nonneg_right hd_sq hJ
  have hscaled :
      (1 + d) ^ 2 * (J + d) ≤ J + η := by
    nlinarith
  let ε : ℝ := d / 120
  have hε : 0 < ε := by positivity
  have hε_small : ε < 1 / 60 := by
    dsimp [ε]
    norm_num
    linarith
  have hε_den : 0 < 1 - 6 * ε := by
    dsimp [ε]
    linarith
  have hperturbationConstant :
      1 / (1 - 6 * ε) ≤ 1 + d := by
    rw [div_le_iff₀ hε_den]
    dsimp [ε]
    nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 19 - d)]
  have hf : ContinuousOn f (Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) := by
    simpa [f] using
      jurkatRichertUpperLinearSieveFactor_zeroEpsilon_continuousOn
  have hMertens₀ :=
    MertensTheorem.tendsto_weightedPrimeReciprocalLogSum
      (a := (1 / 10 : ℝ)) (b := (1 / 3 : ℝ))
      (by norm_num) (by norm_num) hf
  have hMertens :
      Filter.Tendsto
        (fun N : ℕ =>
          MertensTheorem.weightedPrimeReciprocalLogSum
            f N (1 / 10) (1 / 3))
        Filter.atTop (nhds J) := by
    rw [hIntegral] at hMertens₀
    exact hMertens₀
  have hWeighted :
      ∀ᶠ N : ℕ in Filter.atTop,
        MertensTheorem.weightedPrimeReciprocalLogSum
            f N (1 / 10) (1 / 3) ≤ J + d :=
    hMertens.eventually (Iic_mem_nhds (by linarith))
  have hPow :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 10 : ℝ))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hPowLarge :
      ∀ᶠ N : ℕ in Filter.atTop,
        1 / d + 1 < (N : ℝ) ^ (1 / 10 : ℝ) :=
    hPow.eventually (Filter.eventually_gt_atTop (1 / d + 1))
  refine ⟨ε, hε, hε_small, ?_⟩
  filter_upwards [hWeighted, hPowLarge, Filter.eventually_atTop.2
      ⟨2, fun _ h => h⟩] with N hWeightedN hPowN hN
  change
    ∑ q ∈ jurkatRichertSourceMediumPrimes N,
        jurkatRichertUpperLinearSieveFactor
            (jurkatRichertSourceUpperSieveRatio N q ε) /
          ((q : ℝ) - 1) ≤ J + η
  calc
    _ ≤ ∑ q ∈ jurkatRichertSourceMediumPrimes N,
        (1 + d) ^ 2 *
          (f (Real.log q / Real.log N) / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      rcases (Finset.mem_filter.mp hq).2 with
        ⟨hqPrime, hqLower, hqUpper⟩
      have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hqPrime.pos
      have hq_one : 1 < (q : ℝ) := by exact_mod_cast hqPrime.one_lt
      have hq_sub_pos : 0 < (q : ℝ) - 1 := by linarith
      have hqLarge : 1 / d + 1 < (q : ℝ) := lt_trans hPowN hqLower
      have hInv :
          1 / ((q : ℝ) - 1) ≤ (1 + d) / (q : ℝ) := by
        rw [div_le_div_iff₀ hq_sub_pos hq_pos]
        have hInv' : 1 / d < (q : ℝ) - 1 := by linarith
        have hOne : 1 < ((q : ℝ) - 1) * d :=
          (div_lt_iff₀ hd).mp hInv'
        nlinarith
      have hLogMem :
          Real.log q / Real.log N ∈ Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ) :=
        jurkatRichertSourceMediumPrime_log_mem hN hq
      have hFactorNonneg :
          0 ≤ jurkatRichertUpperLinearSieveFactor
            (5 - 10 * (Real.log q / Real.log N)) :=
        jurkatRichertUpperLinearSieveFactor_zeroEpsilon_nonneg hLogMem
      have hFactorPerturb :=
        jurkatRichertUpperLinearSieveFactor_perturbation
          hε hε_small hLogMem
      have hRatio :
          jurkatRichertSourceUpperSieveRatio N q ε =
            5 - 10 * ε - 10 * (Real.log q / Real.log N) := by
        rw [jurkatRichertSourceUpperSieveRatio_eq_zero_sub
            (by omega : 1 < N) hqPrime.pos ε,
          jurkatRichertSourceUpperSieveRatio_zero
            (by omega : 1 < N) hqPrime.pos]
        ring
      rw [hRatio]
      calc
        jurkatRichertUpperLinearSieveFactor
              (5 - 10 * ε - 10 * (Real.log q / Real.log N)) /
            ((q : ℝ) - 1) ≤
            (1 / (1 - 6 * ε) *
                jurkatRichertUpperLinearSieveFactor
                  (5 - 10 * (Real.log q / Real.log N))) /
              ((q : ℝ) - 1) :=
          div_le_div_of_nonneg_right hFactorPerturb hq_sub_pos.le
        _ =
            (1 / (1 - 6 * ε) *
                jurkatRichertUpperLinearSieveFactor
                  (5 - 10 * (Real.log q / Real.log N))) *
              (1 / ((q : ℝ) - 1)) := by ring
        _ ≤
            (1 / (1 - 6 * ε) *
                jurkatRichertUpperLinearSieveFactor
                  (5 - 10 * (Real.log q / Real.log N))) *
              ((1 + d) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hInv
            (mul_nonneg (by positivity) hFactorNonneg)
        _ =
            (1 / (1 - 6 * ε) * (1 + d)) *
              (f (Real.log q / Real.log N) / (q : ℝ)) := by
          dsimp [f]
          ring
        _ ≤
            (1 + d) ^ 2 *
              (f (Real.log q / Real.log N) / (q : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · calc
              1 / (1 - 6 * ε) * (1 + d) ≤
                  (1 + d) * (1 + d) :=
                mul_le_mul_of_nonneg_right hperturbationConstant
                  (by linarith)
              _ = (1 + d) ^ 2 := by ring
          · exact div_nonneg hFactorNonneg hq_pos.le
    _ =
        (1 + d) ^ 2 *
          MertensTheorem.weightedPrimeReciprocalLogSum
            f N (1 / 10) (1 / 3) := by
      rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor (by omega : 1 ≤ N)]
      simp only [MertensTheorem.weightedPrimeReciprocalLogSum]
      rw [Finset.mul_sum]
    _ ≤ (1 + d) ^ 2 * (J + d) :=
      mul_le_mul_of_nonneg_left hWeightedN (sq_nonneg _)
    _ ≤ J + η := hscaled

/-- Prime-q partial summation for the explicit local-density model.  This is the
sole interface that evaluates the q-sum, and its conclusion exhibits Chen's
exact coefficient `8 * (log 8 + K / 2)`. -/
def ChenJurkatRichertVaryingQPrimeSumAsymptotic : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 60 ∧
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        jurkatRichertSourceVaryingQDensityModel N ε ≤
          (8 * (Real.log 8 + jurkatRichertK / 2) + δ) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log N ^ (2 : ℕ)

theorem chenJurkatRichertVaryingQPrimeSumAsymptotic :
    ChenJurkatRichertVaryingQPrimeSumAsymptotic := by
  intro δ hδ
  let B : ℝ := 20 * Real.exp (-Real.eulerMascheroniConstant)
  let J : ℝ :=
    2 * Real.exp Real.eulerMascheroniConstant / 5 *
      (Real.log 8 + jurkatRichertK / 2)
  have hB : 0 < B := by positivity
  have hIntegral :
      (∫ a in (1 / 10 : ℝ)..(1 / 3 : ℝ),
          jurkatRichertUpperLinearSieveFactor (5 - 10 * a) / a) = J := by
    simpa [J] using jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  have hJ : 0 ≤ J := by
    rw [← hIntegral]
    apply intervalIntegral.integral_nonneg
    · norm_num
    · intro a ha
      exact div_nonneg
        (jurkatRichertUpperLinearSieveFactor_zeroEpsilon_nonneg ha)
        (by
          have := ha.1
          norm_num at this ⊢
          linarith)
  let d : ℝ := min 1 (δ / (B + J + 1))
  have hden : 0 < B + J + 1 := by linarith
  have hd : 0 < d := lt_min (by norm_num) (div_pos hδ hden)
  have hd_one : d ≤ 1 := min_le_left _ _
  have hd_δ : d * (B + J + 1) ≤ δ :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hd_sq : d ^ 2 ≤ d := by
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd_one)]
  have hcoefficient :
      (B + d) * (J + d) ≤ B * J + δ := by
    nlinarith
  have hExpCancel :
      Real.exp (-Real.eulerMascheroniConstant) *
          Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add]
    simp
  have hBJ :
      B * J = 8 * (Real.log 8 + jurkatRichertK / 2) := by
    dsimp [B, J]
    calc
      (20 * Real.exp (-Real.eulerMascheroniConstant)) *
            (2 * Real.exp Real.eulerMascheroniConstant / 5 *
              (Real.log 8 + jurkatRichertK / 2)) =
          8 * (Real.exp (-Real.eulerMascheroniConstant) *
              Real.exp Real.eulerMascheroniConstant) *
            (Real.log 8 + jurkatRichertK / 2) := by ring
      _ = 8 * (Real.log 8 + jurkatRichertK / 2) := by rw [hExpCancel]; ring
  obtain ⟨ε, hε, hε_small, hPrimeSum⟩ :=
    eventually_jurkatRichertSource_shiftedPrimeSum_upper d hd
  have hCommon :=
    eventually_jurkatRichertSourceCommonDensity_upper d hd
  refine ⟨ε, hε, hε_small, ?_⟩
  filter_upwards [hPrimeSum, hCommon, Filter.eventually_ge_atTop 2] with
    N hPrimeSumN hCommonN hN
  intro hEven
  let D : ℝ :=
    LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (jurkatRichertSourceBoundingSieve N)
  let P : ℝ :=
    ∑ q ∈ jurkatRichertSourceMediumPrimes N,
      jurkatRichertUpperLinearSieveFactor
          (jurkatRichertSourceUpperSieveRatio N q ε) /
        ((q : ℝ) - 1)
  let M : ℝ :=
    SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ)
  have hLogIntegral :
      0 ≤ LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N :=
    LiuWeight.liuLogarithmicIntegral_nonneg
      (2 / Real.log 2) (by positivity) (by exact_mod_cast hN)
  have hSieveProduct :
      0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (jurkatRichertSourceBoundingSieve N) := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p
        (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero
          (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le
  have hD : 0 ≤ D := mul_nonneg hLogIntegral hSieveProduct
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
        (Nat.cast_nonneg N))
      (sq_nonneg _)
  have hP : P ≤ J + d := by
    simpa [P, J] using hPrimeSumN
  have hCommon' : D ≤ (B + d) * M := by
    dsimp [D, B, M]
    calc
      _ ≤ (20 * Real.exp (-Real.eulerMascheroniConstant) + d) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := hCommonN hEven
      _ = (20 * Real.exp (-Real.eulerMascheroniConstant) + d) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log N ^ (2 : ℕ)) := by ring
  have hJd : 0 ≤ J + d := by linarith
  rw [jurkatRichertSourceVaryingQDensityModel_eq_common_mul]
  change
    D * P ≤
      (8 * (Real.log 8 + jurkatRichertK / 2) + δ) *
        SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ)
  calc
    D * P ≤ D * (J + d) := mul_le_mul_of_nonneg_left hP hD
    _ ≤ ((B + d) * M) * (J + d) :=
      mul_le_mul_of_nonneg_right hCommon' hJd
    _ = ((B + d) * (J + d)) * M := by ring
    _ ≤ (B * J + δ) * M :=
      mul_le_mul_of_nonneg_right hcoefficient hM
    _ =
        (8 * (Real.log 8 + jurkatRichertK / 2) + δ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) := by
      rw [hBJ]
      dsimp [M]
      ring

/-- Chen's aggregate upper-density estimate is derived by applying the generic
fundamental lemma separately at every medium prime.  The additive pointwise
errors are summed using the bounded shifted reciprocal-prime mass and the common
Mertens density. -/
theorem chenJurkatRichertVaryingQUpperDensity_of_fundamentalLemma
    (hfund : DimensionOneUpperRosserDensityFundamentalLemma)
    (ε : ℝ) (hε : 0 < ε) (hεSmall : ε < 1 / 60)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      jurkatRichertSourceVaryingQMainSum N ε ≤
        jurkatRichertSourceVaryingQDensityModel N ε +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) := by
  obtain ⟨K, hK, hlocal⟩ :=
    exists_jurkatRichertSource_dimensionOneLocalProductBound
  let B : ℝ := 20 * Real.exp (-Real.eulerMascheroniConstant) + 1
  let H : ℝ :=
    2 * (Real.log ((1 / 3 : ℝ) / (1 / 10 : ℝ)) + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlogRatio :
      0 < Real.log ((1 / 3 : ℝ) / (1 / 10 : ℝ)) :=
    Real.log_pos (by norm_num)
  have hH : 0 < H := by dsimp [H]; positivity
  let ρ : ℝ := δ / (B * H)
  have hρ : 0 < ρ := div_pos hδ (mul_pos hB hH)
  obtain ⟨z₀, hfundAt⟩ := hfund K ρ hK hρ
  have hPow :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 10 : ℝ))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hCutoffLarge :
      ∀ᶠ N : ℕ in Filter.atTop,
        max z₀ 2 ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    hPow.eventually (Filter.eventually_ge_atTop (max z₀ 2))
  have hReciprocal :=
    eventually_jurkatRichertSource_shiftedPrimeReciprocalSum_le
  have hCommon :=
    eventually_jurkatRichertSourceCommonDensity_upper 1 (by norm_num)
  filter_upwards [hCutoffLarge, hReciprocal, hCommon,
      Filter.eventually_ge_atTop 2] with N hCutoffN hReciprocalN hCommonN hN
  intro hEven
  let Q := jurkatRichertSourceMediumPrimes N
  let D : ℝ :=
    LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (jurkatRichertSourceBoundingSieve N)
  let R : ℝ := ∑ q ∈ Q, 1 / ((q : ℝ) - 1)
  let M : ℝ :=
    SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ)
  have hNOne : 1 < N := by omega
  have hPointwise :
      ∀ q ∈ Q,
        (jurkatRichertSourceConditionedBoundingSieve N q).mainSum
            (jurkatRichertSourceVaryingQUpperRosserWeight N q ε) ≤
          (jurkatRichertUpperLinearSieveFactor
              (jurkatRichertSourceUpperSieveRatio N q ε) + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
              (jurkatRichertSourceConditionedBoundingSieve N q) := by
    intro q hqQ
    have hq : q ∈ jurkatRichertSourceMediumPrimes N := by
      simpa [Q] using hqQ
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2.1
    have hDelta :
        0 < (N : ℝ) ^ (1 / 2 - ε) / (q : ℝ) :=
      div_pos (Real.rpow_pos_of_pos (by positivity) _)
        (by exact_mod_cast hqPrime.pos)
    have hRatio :=
      jurkatRichertSourceUpperSieveRatio_mem hNOne hε hεSmall hq
    have hbound :=
      hfundAt (jurkatRichertSourceConditionedBoundingSieve N q)
        ((N : ℝ) ^ (1 / 10 : ℝ))
        ((N : ℝ) ^ (1 / 2 - ε) / (q : ℝ))
        (jurkatRichertSourceUpperSieveRatio N q ε)
        (le_trans (le_max_left _ _) hCutoffN)
        (le_trans (le_max_right _ _) hCutoffN) hDelta
        (jurkatRichertSourceConditioned_dimensionOneLocalProductBound
          (hlocal N))
        (jurkatRichertSourceConditioned_primeFactor_le_cutoff N q)
        rfl hRatio.1 hRatio.2
    change
      (jurkatRichertSourceConditionedBoundingSieve N q).mainSum
          (LinearSieve.upperRosserWeight
            (jurkatRichertSourceSiftingProduct N)
            (Nat.floor ((N : ℝ) ^ (1 / 2 - ε) / (q : ℝ)) + 1)) ≤ _
    exact hbound
  have hMassNonneg :
      ∀ q ∈ Q, 0 ≤
        (jurkatRichertSourceConditionedBoundingSieve N q).totalMass := by
    intro q hqQ
    have hq : q ∈ jurkatRichertSourceMediumPrimes N := by
      simpa [Q] using hqQ
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2.1
    change 0 ≤
      LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N /
        ((q : ℝ) - 1)
    apply div_nonneg
    · exact LiuWeight.liuLogarithmicIntegral_nonneg
        (2 / Real.log 2) (by positivity) (by exact_mod_cast hN)
    · have hqOne : (1 : ℝ) < q := by exact_mod_cast hqPrime.one_lt
      linarith
  have hD : 0 ≤ D := by
    dsimp [D]
    apply mul_nonneg
    · exact LiuWeight.liuLogarithmicIntegral_nonneg
        (2 / Real.log 2) (by positivity) (by exact_mod_cast hN)
    · unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
      apply Finset.prod_nonneg
      intro p hp
      exact sub_nonneg.mpr
        ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p
          (Nat.prime_of_mem_primeFactors hp)
          ((Nat.mem_primeFactors_of_ne_zero
            (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le
  have hR : 0 ≤ R := by
    dsimp [R, Q]
    apply Finset.sum_nonneg
    intro q hq
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2.1
    have hqOne : (1 : ℝ) < q := by exact_mod_cast hqPrime.one_lt
    positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
        (Nat.cast_nonneg N))
      (sq_nonneg _)
  have hCommon' : D ≤ B * M := by
    dsimp [D, B, M]
    convert hCommonN hEven using 1
    all_goals ring
  have hReciprocal' : R ≤ H := by
    simpa [R, Q, H] using hReciprocalN
  have hError : ρ * D * R ≤ δ * M := by
    calc
      ρ * D * R ≤ ρ * (B * M) * R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCommon' hρ.le) hR
      _ ≤ ρ * (B * M) * H :=
        mul_le_mul_of_nonneg_left hReciprocal'
          (mul_nonneg hρ.le (mul_nonneg hB.le hM))
      _ = δ * M := by
        dsimp [ρ]
        field_simp [hB.ne', hH.ne']
  calc
    jurkatRichertSourceVaryingQMainSum N ε ≤
        ∑ q ∈ Q,
          (jurkatRichertSourceConditionedBoundingSieve N q).totalMass *
            ((jurkatRichertUpperLinearSieveFactor
                (jurkatRichertSourceUpperSieveRatio N q ε) + ρ) *
              AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                (jurkatRichertSourceConditionedBoundingSieve N q)) := by
      unfold jurkatRichertSourceVaryingQMainSum
      change (∑ q ∈ Q, _) ≤ _
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hPointwise q hq) (hMassNonneg q hq)
    _ = jurkatRichertSourceVaryingQDensityModel N ε + ρ * D * R := by
      rw [jurkatRichertSourceVaryingQDensityModel_eq_common_mul]
      dsimp [D, R, Q]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      change
        (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N /
            ((q : ℝ) - 1)) *
              ((jurkatRichertUpperLinearSieveFactor
                  (jurkatRichertSourceUpperSieveRatio N q ε) + ρ) *
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                  (jurkatRichertSourceBoundingSieve N)) =
          (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
              AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                (jurkatRichertSourceBoundingSieve N)) *
              (jurkatRichertUpperLinearSieveFactor
                  (jurkatRichertSourceUpperSieveRatio N q ε) /
                ((q : ℝ) - 1)) +
            ρ *
                (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
                  AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                    (jurkatRichertSourceBoundingSieve N)) *
              (1 / ((q : ℝ) - 1))
      ring
    _ ≤ jurkatRichertSourceVaryingQDensityModel N ε + δ * M :=
      add_le_add_right hError _
    _ = jurkatRichertSourceVaryingQDensityModel N ε +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) := by
      dsimp [M]
      ring

/-- The standard aggregate distribution input for the exact level-`D/q`
remainders.  The explicit Rosser coefficient is the weight to which
Bombieri--Vinogradov is applied. -/
def ChenJurkatRichertVaryingQUpperDistribution : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
    ∀ δ : ℝ, 0 < δ →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        jurkatRichertSourceVaryingQRemainderSum N ε ≤
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ)

/-- The source-faithful `3^ω`-weighted Bombieri--Vinogradov interface implies
the exact varying-`q` upper-distribution statement.  The proof expands
`upperErrSum`, uses standard AP errors only on the reduced `q ∤ N` lanes, and
absorbs the nonreduced lanes and source exceptional-prime corrections through
the preceding unconditional power-saving theorem. -/
theorem chenJurkatRichertVaryingQUpperDistribution_of_weightedBV
    (hBV : ChenJurkatRichertVaryingQWeightedBombieriVinogradov) :
    ChenJurkatRichertVaryingQUpperDistribution := by
  intro ε hε hεSixth δ hδ
  rcases hBV ε hε hεSixth 3 (by norm_num) with ⟨C, hC, hBVeventually⟩
  let U := SingularSeries.liuUniversalProduct
  have hU : 0 < U := by
    simpa [U] using SingularSeries.liuUniversalProduct_pos
  let cerr := 4 * C / ((δ / 2) * U)
  obtain ⟨N₀, hcerr⟩ := errLogCube_negligible cerr
  have hcorrection :=
    eventually_jurkatRichertSourceVaryingQUnconditionalCorrection_le
      ε (δ / 2) hε (by linarith)
  filter_upwards [hBVeventually, hcorrection,
      Filter.eventually_ge_atTop (max N₀ 3)] with
      N hBVN hcorrectionN hN
  intro hEven
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNthree : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hδU : 0 < (δ / 2) * U := mul_pos (by linarith) hU
  have hBVbound :
      jurkatRichertSourceReducedWeightedBVSum N ε ≤
        C * (N : ℝ) / Real.log N ^ (3 : ℕ) := by
    simpa [Real.rpow_natCast] using hBVN
  have hcerrN := hcerr N hN₀ hEven
  have hBVtiny :
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
        ((δ / 2) * U / 16) * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hcerrN
      (show 0 ≤ (δ / 2) * U / 4 by positivity)
    calc
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) =
          ((δ / 2) * U / 4) *
            (cerr * (N : ℝ) / Real.log N ^ (3 : ℕ)) := by
        dsimp [cerr]
        field_simp [hδU.ne']
      _ ≤ ((δ / 2) * U / 4) *
          ((1 / 4 : ℝ) * (N : ℝ) / Real.log N ^ (2 : ℕ)) := hscaled
      _ = ((δ / 2) * U / 16) * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by ring
  have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℕ) := by positivity
  have hUle : U ≤ SingularSeries.liuSingularSeries N := by
    simpa [U] using SingularSeries.liuUniversalProduct_le_liuSingularSeries N
  have hcoeff :
      (δ / 2) * U / 16 ≤
        (δ / 2) * SingularSeries.liuSingularSeries N := by
    calc
      (δ / 2) * U / 16 = ((δ / 2) / 16) * U := by ring
      _ ≤ ((δ / 2) / 16) * SingularSeries.liuSingularSeries N :=
        mul_le_mul_of_nonneg_left hUle (by positivity)
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact (SingularSeries.liuSingularSeries_pos N).le
  have hBVsmall :
      jurkatRichertSourceReducedWeightedBVSum N ε ≤
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
    calc
      jurkatRichertSourceReducedWeightedBVSum N ε ≤
          C * (N : ℝ) / Real.log N ^ (3 : ℕ) := hBVbound
      _ ≤ ((δ / 2) * U / 16) * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := hBVtiny
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
        simpa [mul_div_assoc] using
          mul_le_mul_of_nonneg_right hcoeff hscale
  have hfinite :=
    jurkatRichertSourceVaryingQRemainderSum_le_weightedBV_add_correction
      N ε hEven (by omega)
  calc
    jurkatRichertSourceVaryingQRemainderSum N ε ≤
        jurkatRichertSourceReducedWeightedBVSum N ε +
          jurkatRichertSourceVaryingQUnconditionalCorrection N ε := hfinite
    _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) +
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) :=
      add_le_add hBVsmall hcorrectionN
    _ = δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by ring

/-- The only two standard analytic inputs for the varying-q upper sieve are the
generic dimension-one upper fundamental lemma and the source-faithful weighted
Bombieri--Vinogradov estimate.  Prime-q partial summation is proved internally. -/
def ChenJurkatRichertVaryingQUpperSieveStandardInput : Prop :=
  DimensionOneUpperRosserDensityFundamentalLemma ∧
    ChenJurkatRichertVaryingQWeightedBombieriVinogradov

/-- The aggregate upper asymptotic, retained as a derived statement for the
weighted-count algebra below. -/
def ChenJurkatRichertVaryingQUpperSieveAsymptotic : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      jurkatRichertSourceMediumPrimeAggregate N ≤
        (jurkatRichertQ1MainCoefficient jurkatRichertK + η) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ)

/-- The explicit q-conditioned upper Rosser inequalities, the generic density
fundamental lemma, unconditional prime-q partial summation, and the distribution
estimate derived from weighted Bombieri--Vinogradov recover Chen's coefficient
`8 * (log 8 + K / 2)`. -/
theorem chenJurkatRichertVaryingQUpperSieveAsymptotic_of_standardInput
    (hinput : ChenJurkatRichertVaryingQUpperSieveStandardInput) :
    ChenJurkatRichertVaryingQUpperSieveAsymptotic := by
  intro η hη
  let δ := η / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  rcases chenJurkatRichertVaryingQPrimeSumAsymptotic δ hδ with
    ⟨ε, hε, hεSmall, hmodel⟩
  have hmain :=
    chenJurkatRichertVaryingQUpperDensity_of_fundamentalLemma
      hinput.1 ε hε hεSmall δ hδ
  have hdistribution :=
    chenJurkatRichertVaryingQUpperDistribution_of_weightedBV hinput.2
  have hrem :=
    hdistribution ε hε (lt_trans hεSmall (by norm_num)) δ hδ
  filter_upwards [hmain, hmodel, hrem,
      Filter.eventually_ge_atTop 2] with N hmainN hmodelN hremN hN
  intro hEven
  have hmainN' := hmainN hEven
  have hmodelN' := hmodelN hEven
  have hremN' := hremN hEven
  have hfinite :=
    jurkatRichertSourceMediumPrimeAggregate_le_main_add_remainder
      N ε (by omega) hεSmall
  let M : ℝ :=
    SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ)
  have hmainN'' :
      jurkatRichertSourceVaryingQMainSum N ε ≤
        jurkatRichertSourceVaryingQDensityModel N ε + δ * M := by
    convert hmainN' using 1
    dsimp [M]
    ring
  have hmodelN'' :
      jurkatRichertSourceVaryingQDensityModel N ε ≤
        (8 * (Real.log 8 + jurkatRichertK / 2) + δ) * M := by
    convert hmodelN' using 1
    dsimp [M]
    ring
  have hremN'' :
      jurkatRichertSourceVaryingQRemainderSum N ε ≤ δ * M := by
    convert hremN' using 1
    dsimp [M]
    ring
  calc
    jurkatRichertSourceMediumPrimeAggregate N ≤
        jurkatRichertSourceVaryingQMainSum N ε +
          jurkatRichertSourceVaryingQRemainderSum N ε :=
      hfinite
    _ ≤
        (jurkatRichertSourceVaryingQDensityModel N ε + δ * M) + δ * M := by
      exact add_le_add hmainN'' hremN''
    _ ≤
        ((8 * (Real.log 8 + jurkatRichertK / 2) + δ) * M + δ * M) +
          δ * M := by
      gcongr
    _ = (jurkatRichertQ1MainCoefficient jurkatRichertK + η) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) := by
      unfold jurkatRichertQ1MainCoefficient
      dsimp [δ, M]
      ring

/-- Chen's equations (26)--(27), with the exact finite source weight exposed:
the base lower sieve and varying-`q` upper sieve imply the published distinct
weighted lower bound.  The elementary integral estimate is internal. -/
theorem chenJurkatRichertDistinctWeightedLowerBound_of_asymptotics
    (hbase : ChenJurkatRichertBaseLowerSieveAsymptotic)
    (hupper : ChenJurkatRichertVaryingQUpperSieveStandardInput) :
    ChenJurkatRichertDistinctWeightedLowerBound := by
  have hupper' :=
    chenJurkatRichertVaryingQUpperSieveAsymptotic_of_standardInput hupper
  intro η hη
  have hbase' := hbase (η / 2) (by linarith)
  have hupper'' := hupper' η hη
  filter_upwards
      [hbase', hupper'', Filter.eventually_ge_atTop 2] with N hbaseN hupperN hN
  intro hEven
  have hbaseN' := hbaseN hEven
  have hupperN' := hupperN hEven
  let M : ℝ :=
    SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ)
  have hMpos : 0 < M := by
    dsimp [M]
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact div_pos
      (mul_pos (SingularSeries.liuSingularSeries_pos N) hNpos)
      (pow_pos hlogpos _)
  have hcoefficient :
      (2.6408 : ℝ) ≤
        jurkatRichertBaseMainCoefficient jurkatRichertJ -
          jurkatRichertQ1MainCoefficient jurkatRichertK / 2 :=
    jurkatRichert_mainCoefficient_ge_twoPoint6408
      jurkatRichertJ jurkatRichertK jurkatRichert_integralEstimate
  have hbaseM :
      (jurkatRichertBaseMainCoefficient jurkatRichertJ - η / 2) * M ≤
        ((jurkatRichertSourceCandidates N).card : ℝ) := by
    convert hbaseN' using 1
    dsimp [M]
    ring
  have hupperM :
      jurkatRichertSourceMediumPrimeAggregate N ≤
        (jurkatRichertQ1MainCoefficient jurkatRichertK + η) * M := by
    convert hupperN' using 1
    dsimp [M]
    ring
  have htarget :
      (2.6408 - η) * M ≤
        ((jurkatRichertSourceCandidates N).card : ℝ) -
          jurkatRichertSourceMediumPrimeAggregate N / 2 := by
    nlinarith
  rw [jurkatRichertSourceWeightedCount_eq]
  convert htarget using 1
  dsimp [M]
  ring


/-- For large `N`, prime-factor multiplicity is at most 10: for `q ≥ z`, `n ≤ N`, and `N > 2^110`,
`v_q(n) ≤ 10`, since `q^{11} > N`. -/
private theorem factorization_le_ten_of_large {N q : ℕ} (hq : q.Prime)
    (hqz : correctedChenZ N ≤ q) (hNbig : 2 ^ 110 < N) (n : ℕ) (hn : n ≤ N) :
    n.factorization q ≤ 10 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hq11 : (N : ℝ) < (q : ℝ) ^ 11 := by
      let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
      have hz_ge : (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ (correctedChenZ N : ℝ) :=
        chenZ_ge_root_half N hNbig
      have hqge : (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ (q : ℝ) :=
        le_trans hz_ge (by exact_mod_cast hqz)
      have hN10 : (2 ^ 11 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := chenZ_root_large N hNbig
      have hx10 : x ^ 10 = (N : ℝ) := by
        dsimp [x]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (le_of_lt hNpos)]
        norm_num
      have hx11 : x ^ 11 = (N : ℝ) * x := by
        rw [show x ^ 11 = x * x ^ 10 by rw [pow_succ']]
        rw [hx10]
        ring
      have hxdiv : (1 : ℝ) < x / 2 ^ 11 := by
        rw [one_lt_div (by positivity : (0 : ℝ) < 2 ^ 11)]
        dsimp [x]
        exact hN10
      have hpow11' : (x / 2) ^ 11 ≤ (q : ℝ) ^ 11 := by
        dsimp [x]
        apply pow_le_pow_left₀
        · positivity
        · exact hqge
      have hgt : (N : ℝ) < (x / 2) ^ 11 := by
        rw [div_pow, hx11]
        have h1 : (N : ℝ) * 1 < (N : ℝ) * (x / 2 ^ 11) := by
          exact mul_lt_mul_of_pos_left hxdiv hNpos
        simpa [mul_div_assoc, mul_one] using h1
      exact lt_of_lt_of_le (by simpa [x] using hgt) hpow11'
    have hdvd : q ^ n.factorization q ∣ n :=
      (Nat.Prime.pow_dvd_iff_le_factorization hq hn0).mpr le_rfl
    have hqpow_le_n : (q : ℝ) ^ n.factorization q ≤ (n : ℝ) := by
      exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd)
    by_contra hnot
    have h11 : 11 ≤ n.factorization q := by
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
    have hqpow11 : (q : ℝ) ^ 11 ≤ (q : ℝ) ^ n.factorization q :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ q from hq.pos)) h11
    have hqpow_le_N : (q : ℝ) ^ n.factorization q ≤ (N : ℝ) :=
      le_trans hqpow_le_n (by exact_mod_cast hn)
    have hNlt : (N : ℝ) < (q : ℝ) ^ n.factorization q := lt_of_lt_of_le hq11 hqpow11
    exact (not_lt_of_ge hqpow_le_N hNlt).elim

/-- Uniform bound for the proper-power part: `Σ_p Σ_{q ∈ [z,y), q²|N-p} v_q(N-p) ≤ 60·N^{9/10}`,
combining multiplicity ≤ 10 with the `6·N^{9/10}` counting bound. -/
theorem correctedChenProperPowerSum_le_negligible (N : ℕ) (hNbig : 2 ^ 110 < N)
    (hEven : Even N) :
    (correctedChenCandidates N).sum (fun p =>
      ∑ q ∈ (Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
        ((N - p).factorization q : ℝ)) ≤
      60 * (N : ℝ) ^ (9 / 10 : ℝ) := by
  have h10 : ∀ p ∈ correctedChenCandidates N,
      ∀ q ∈ (Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
        (N - p).factorization q ≤ 10 := by
    intro p hp q hq
    rcases Finset.mem_filter.mp hq with ⟨hqr, hc⟩
    have hqz : correctedChenZ N ≤ q := hc.2.1
    have hpN : p < N := by
      rcases Finset.mem_filter.mp hp with ⟨hpN, _⟩
      simpa using hpN
    exact factorization_le_ten_of_large hc.1 hqz hNbig (N - p) (by omega)
  have hsum : (correctedChenCandidates N).sum (fun p =>
      ∑ q ∈ (Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
        ((N - p).factorization q : ℝ)) ≤
    (correctedChenCandidates N).sum (fun p =>
      (10 * ((Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hper : ∀ q ∈ (Finset.range (correctedChenY N)).filter
        (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
      ((N - p).factorization q : ℝ) ≤ (10 : ℝ) := by
      intro q hq
      exact_mod_cast h10 p hp q hq
    calc
      (∑ q ∈ (Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
        ((N - p).factorization q : ℝ)) ≤
          ∑ q ∈ (Finset.range (correctedChenY N)).filter
            (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p), (10 : ℝ) :=
            Finset.sum_le_sum hper
      _ = (10 * ((Finset.range (correctedChenY N)).filter
            (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
  have hb' : (correctedChenCandidates N).sum (fun p =>
      ((Finset.range (correctedChenY N)).filter
        (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card) ≤
      6 * (N : ℝ) ^ (9 / 10 : ℝ) :=
    correctedChenPrimePowerProperCountBound N hNbig hEven
  have hbreal : (correctedChenCandidates N).sum (fun p =>
      (((Finset.range (correctedChenY N)).filter
        (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card : ℝ)) ≤
      6 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    exact_mod_cast hb'
  calc
    (correctedChenCandidates N).sum (fun p =>
      ∑ q ∈ (Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
        ((N - p).factorization q : ℝ)) ≤
    (correctedChenCandidates N).sum (fun p =>
      (10 * ((Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card : ℝ)) := hsum
    _ = 10 * (correctedChenCandidates N).sum (fun p =>
          (((Finset.range (correctedChenY N)).filter
            (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ 10 * (6 * (N : ℝ) ^ (9 / 10 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hbreal (by norm_num)
    _ = 60 * (N : ℝ) ^ (9 / 10 : ℝ) := by ring

/-- **Reduction of the prime-power penalty sum**: for even `N > 2^110`,

  Σ_p primePowerSum(N-p) ≤ q¹ count + 60·N^{9/10},

where the q¹ count `= Σ_p #{q ∈ [z,y) : q | N-p}` is the only remaining analytic input,
to be paired with weighted Pan distribution bounds; the proper-power part is absorbed by `60·N^{9/10}`. -/
theorem correctedChenPrimePowerSum_le_q1Count_add_negligible (N : ℕ)
    (hNbig : 2 ^ 110 < N) (hEven : Even N) :
    (correctedChenCandidates N).sum
        (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      correctedChenQ1Count N + 60 * (N : ℝ) ^ (9 / 10 : ℝ) := by
  have hper : ∀ p ∈ correctedChenCandidates N,
      primePowerSum (N - p) (correctedChenZ N) (correctedChenY N) ≤
        ((Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card +
        (∑ q ∈ (Finset.range (correctedChenY N)).filter
            (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
          ((N - p).factorization q : ℝ)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpN, _⟩
    have hnp : N - p ≠ 0 := by
      have hpN' : p < N := by simpa using hpN
      have hge2 : 2 ≤ N - p := by
        rcases Finset.mem_filter.mp hp with ⟨_, hc⟩
        exact hc.2.1
      omega
    exact primePowerSum_le_factorCount_add_powerSum (N - p) (correctedChenZ N)
      (correctedChenY N) hnp
  calc
    (correctedChenCandidates N).sum
        (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      (correctedChenCandidates N).sum (fun p =>
        ((Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card +
        (∑ q ∈ (Finset.range (correctedChenY N)).filter
            (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
          ((N - p).factorization q : ℝ))) :=
        Finset.sum_le_sum hper
    _ = (correctedChenCandidates N).sum (fun p =>
          ((Finset.range (correctedChenY N)).filter
            (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card) +
        (correctedChenCandidates N).sum (fun p =>
          ∑ q ∈ (Finset.range (correctedChenY N)).filter
              (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p),
            ((N - p).factorization q : ℝ)) := by
          rw [Finset.sum_add_distrib]
          conv => rhs; rw [Nat.cast_sum]
    _ ≤ correctedChenQ1Count N + 60 * (N : ℝ) ^ (9 / 10 : ℝ) := by
          unfold correctedChenQ1Count
          rw [Nat.cast_sum]
          exact add_le_add le_rfl (correctedChenProperPowerSum_le_negligible N hNbig hEven)


/-- Exact finite separation between the literature's distinct-q weight and the
valuation-weighted corrected endpoint.  Proper powers cost at most
`30 * N^(9/10)` after the factor `1/2` in the Richert weight. -/
theorem jurkatRichertDistinctWeightedCount_sub_proper_le
    (N : ℕ) (hNbig : 2 ^ 110 < N) (hEven : Even N) :
    jurkatRichertDistinctWeightedCount N -
        30 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
      jurkatRichertWeightedCount N := by
  have hred :=
    correctedChenPrimePowerSum_le_q1Count_add_negligible N hNbig hEven
  unfold jurkatRichertDistinctWeightedCount jurkatRichertWeightedCount
    correctedChenPrimePowerPenalty
  nlinarith

/-- The proper-prime-power error is absorbed into an arbitrary positive
multiple of the genuine Liu singular-series main scale.  This uses the positive
universal Euler-product lower bound, not a fixed q1 coefficient. -/
theorem eventually_correctedChenProperPowerError_le_liuSingularSeries
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
        ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
  have hcore :
      Filter.Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) ^ (2 : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ))
        Filter.atTop (nhds 0) := by
    exact
      ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 10)).tendsto_div_nhds_zero).comp
          tendsto_natCast_atTop_atTop
  have heq :
      (fun N : ℕ => 60 *
        (Real.log (N : ℝ) ^ (2 : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ))) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        (60 * (N : ℝ) ^ (9 / 10 : ℝ)) /
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ))) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num,
      Real.rpow_sub hNpos, Real.rpow_one, ← Real.rpow_natCast]
    field_simp [hNpos.ne', hlogpos.ne']
    norm_num [Real.rpow_natCast]
  have hratio :
      Filter.Tendsto (fun N : ℕ =>
        (60 * (N : ℝ) ^ (9 / 10 : ℝ)) /
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)))
        Filter.atTop (nhds 0) := by
    exact ((hcore.const_mul 60).congr' heq).trans (by simp)
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop,
      (60 * (N : ℝ) ^ (9 / 10 : ℝ)) /
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) ≤
        ρ * SingularSeries.liuUniversalProduct :=
    hratio.eventually (Iic_mem_nhds
      (mul_pos hρ SingularSeries.liuUniversalProduct_pos))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 2] with N hsmallN hN
  have hseries :
      ρ * SingularSeries.liuUniversalProduct ≤
        ρ * SingularSeries.liuSingularSeries N :=
    mul_le_mul_of_nonneg_left
      (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hρ.le
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) :=
    div_pos hNpos (pow_pos hlogpos _)
  rw [div_le_iff₀ hscale] at hsmallN
  calc
    60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
        (ρ * SingularSeries.liuUniversalProduct) *
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := hsmallN
    _ ≤ (ρ * SingularSeries.liuSingularSeries N) *
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hseries hscale.le
    _ = ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by ring

/-- The source-faithful distinct-medium-prime theorem produces the canonical
valuation-weighted JR endpoint.  The finite lower-floor and exceptional-fibre
loss is combined with the proper-prime-power loss and absorbed into the main
scale; the triple penalty remains outside this theorem. -/
theorem chenJurkatRichertWeightedLowerBound_of_distinct
    (hJR : ChenJurkatRichertDistinctWeightedLowerBound) :
    ChenJurkatRichertWeightedLowerBound := by
  intro η hη
  have hsource := hJR (η / 2) (by linarith)
  have hproper :=
    eventually_correctedChenProperPowerError_le_liuSingularSeries
      (η / 2) (by linarith)
  filter_upwards
      [hsource, hproper, Filter.eventually_ge_atTop (2 ^ 110 + 1)] with
      N hsourceN hproperN hN
  intro hEven
  have hboundary :=
    jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N (by omega) hEven
  have hfinite :=
    jurkatRichertDistinctWeightedCount_sub_proper_le N (by omega) hEven
  let M : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) /
    Real.log N ^ (2 : ℕ)
  have hsourceN' : (2.6408 - η / 2) * M ≤
      jurkatRichertSourceWeightedCount N := by
    convert hsourceN hEven using 1
    · dsimp [M]
      ring
  have hproperN' : 60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤ (η / 2) * M := by
    convert hproperN using 1
    · dsimp [M]
      ring
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by positivity
  have htarget :
      (2.6408 - η) * M ≤ jurkatRichertWeightedCount N := by
    nlinarith
  convert htarget using 1
  · dsimp [M]
    ring


/-! ## Conditional q¹ distribution bound and its analytic inputs

This section formulates the q¹ analytic input: the weighted Pan mean-value theorem
`AnalyticNumberTheory.Sieve.PanMeanValueUniform` is assembled by
`of_sourceFaithfulSignedInputs` from two character mean-value bounds and a signed main-term bound
(see the Pan bridge). With the required aggregate estimates,
the goal is `hq1`, a uniform upper bound for `correctedChenQ1Count N`:

  `q1Count(N) ≤ Cq · 𝔖_trunc(N, z−1) · N/log²N`.

The conditional proof chain is:

1. **Finite reindexing**: `correctedChenQ1Count_eq_reindexed` turns `Σ_p #{q | N-p}`
   into `Σ_q #{p ∈ candidates : q | N-p}`, for primes q ∈ [z,y).
2. **Structural reduction**: the candidate AP count is expanded by two layers of Möbius inversion.
   First, candidates are the unsifted support restricted by coprimality with `P_sift`.
   Second, the unsifted support is expanded using the forbidden-prime product `P_forb`.
   This reduces to prime-AP base counts `q1APBaseCount N m` and gives the exact algebraic inequality
   `q1Count ≤ q1MainTermSum N + q1ErrorTermSum N`.
3. **Main-term absorption**: `q1MainTermAbsorption` bounds the main term using the singular series
   `singularSeriesTruncated` and the prime-reciprocal range bound `primeReciprocalSum_range_le`,
   absorbing it into `C₁·𝔖_trunc·N/log²N`.
4. **Uniform error bound**: `q1APErrorUniformBound` is an output required of a weighted q¹ aggregate theorem
   for the full double Möbius error sum. One cannot insert all divisors of the sifting product
   and their `3^ω`-weighted lcm fibers, without truncation, into the classical Pan/Bombieri--Vinogradov theorem,
   which controls only `m ≤ N^(1/2)/log(N)^B`.
5. **Assembly**: `hq1_of_q1AnalyticInputs` combines these two analytic inputs with elementary
   logarithmic estimates and `𝔖_trunc ≥ 1/2` to give `∃ Cq Nq, hq1`.

Parity: for an even modulus `m`, the AP base count can contain only `p = 2`, requiring `m | N-2`.
Thus `q1APMainValue` uses the **exact value**, 0 or 1, for even moduli, and the error vanishes
by `q1APError_even_zero`. Odd moduli use the main term `li(N)/φ(m)`. This avoids the degeneracy
of the Möbius main term at the `r = 2` factor, as in the classical treatment.
-/

-- The large double Möbius expansion needs an increased rewriting/simplification heartbeat budget.
set_option maxHeartbeats 1000000


end MathlibNt.SieveTheory.SwitchingPrinciple
