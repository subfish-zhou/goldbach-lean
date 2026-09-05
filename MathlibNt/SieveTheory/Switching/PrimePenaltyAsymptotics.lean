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

/-- The generic dimension-one upper fundamental lemma for the explicit Rosser
coefficient.  The only analytic input is local: for a sieve whose primes lie
below `z`, at real level `Δ` and ratio `s = log Δ / log z`, the Rosser density
sum is at most `(F(s) + ρ) V(S)`. -/
def DimensionOneUpperRosserDensityFundamentalLemma : Prop :=
  ∀ K ρ : ℝ, 1 < K → 0 < ρ →
    ∃ z₀ : ℝ, ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 2 ≤ z → 0 < Δ →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z →
      3 / 2 ≤ s → s ≤ 4 →
      S.mainSum
          (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
        (jurkatRichertUpperLinearSieveFactor s + ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S

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

/-- Reindexing the q¹ count: `Σ_p #{q ∈ [z,y) : q | N-p} =
Σ_{q ∈ [z,y)} #{p ∈ candidates : q | N−p}`. -/
theorem correctedChenQ1Count_eq_reindexed (N : ℕ) :
    correctedChenQ1Count N =
      ∑ q ∈ (Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q),
        (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ) := by
  unfold correctedChenQ1Count
  let Q : Finset ℕ := (Finset.range (correctedChenY N)).filter
    (fun q => q.Prime ∧ correctedChenZ N ≤ q)
  have h2 : (correctedChenCandidates N).sum (fun p =>
        (((Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card : ℝ)) =
      (correctedChenCandidates N).sum (fun p =>
        ∑ q ∈ Q, if q ∣ N - p then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.card_filter]
    rw [Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [← Finset.sum_filter]
    rw [Finset.sum_filter]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hd : q ∣ N - p <;> simp [hd]
  have h3 : (correctedChenCandidates N).sum (fun p =>
        ∑ q ∈ Q, if q ∣ N - p then (1 : ℝ) else 0) =
      ∑ q ∈ Q, (correctedChenCandidates N).sum (fun p =>
        if q ∣ N - p then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
  have h4 : ∑ q ∈ Q, (correctedChenCandidates N).sum (fun p =>
        if q ∣ N - p then (1 : ℝ) else 0) =
      ∑ q ∈ Q, (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_boole]
  exact h2.trans (h3.trans h4)

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

/-- **Deriving hPrimePower from its inputs**: suppose the q¹ count satisfies the uniform upper bound
`q¹Count(N) ≤ Cq·𝔖_trunc·N/log²N`, from a weighted Pan/distribution input,
and the proper-power part is negligible. Then `hPrimePower` holds, namely
`Σ_p primePowerSum(N−p) ≤ (Cq + 1/2)·𝔖_trunc·N/log²N`. -/
theorem hPrimePower_of_q1Count_bound
    (hq1 : ∃ Cq : ℝ, 0 < Cq ∧ ∃ Nq : ℕ, ∀ N : ℕ, Nq ≤ N → Even N →
      correctedChenQ1Count N ≤ Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2)
    (hneg : ∃ Nn : ℕ, ∀ N : ℕ, Nn ≤ N → Even N →
      60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
        (1 / 2 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧ ∃ N₀ₚ : ℕ, ∀ N : ℕ, N₀ₚ ≤ N → Even N →
      (correctedChenCandidates N).sum
          (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        Cₚ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := by
  rcases hq1 with ⟨Cq, hCq, Nq, hq1'⟩
  rcases hneg with ⟨Nn, hneg'⟩
  refine ⟨Cq + 1 / 2, by positivity, max (max Nq Nn) (2 ^ 110 + 1), ?_⟩
  intro N hN hEven
  have hNq : Nq ≤ N := by
    dsimp at hN
    omega
  have hNn : Nn ≤ N := by
    dsimp at hN
    omega
  have hNbig : 2 ^ 110 < N := by
    dsimp at hN
    omega
  let 𝔖 : ℝ := AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
  let X : ℝ := (N : ℝ) / (log (N : ℝ)) ^ 2
  have hred := correctedChenPrimePowerSum_le_q1Count_add_negligible N hNbig hEven
  have hXeq1 : Cq * 𝔖 * X =
      Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        (N : ℝ) / (log (N : ℝ)) ^ 2 := by
    dsimp [𝔖, X]
    ring
  have hXeq2 : (1 / 2 : ℝ) * 𝔖 * X =
      (1 / 2 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        (N : ℝ) / (log (N : ℝ)) ^ 2 := by
    dsimp [𝔖, X]
    ring
  have hq1'' : correctedChenQ1Count N ≤ Cq * 𝔖 * X := by
    dsimp [𝔖, X]
    rw [hXeq1]
    exact hq1' N hNq hEven
  have hneg'' : 60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤ (1 / 2 : ℝ) * 𝔖 * X := by
    dsimp [𝔖, X]
    rw [hXeq2]
    exact hneg' N hNn hEven
  have hXeq : (Cq + 1 / 2) * 𝔖 * X =
      (Cq + 1 / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
    dsimp [𝔖, X]
    ring
  calc
    (correctedChenCandidates N).sum
        (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      correctedChenQ1Count N + 60 * (N : ℝ) ^ (9 / 10 : ℝ) := hred
    _ ≤ Cq * 𝔖 * X + (1 / 2 : ℝ) * 𝔖 * X := by
          exact add_le_add hq1'' hneg''
    _ = (Cq + 1 / 2) * 𝔖 * X := by ring
    _ = (Cq + 1 / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
          exact hXeq

/-- **Negligibility threshold for proper powers**: for sufficiently large even `N`,
`60·N^{9/10} ≤ (1/2)·𝔖_trunc·N/log²N`. This follows directly from `𝔖 ≥ 1/2` and the elementary growth bound
`240·log²N ≤ N^{1/10}`, using `log = o(N^{1/20})`. It discharges
the `hneg` input of `hPrimePower_of_q1Count_bound`, leaving only the q¹ distribution bound. -/
theorem properPower_negligible_threshold :
    ∃ Nn : ℕ, ∀ N : ℕ, Nn ≤ N → Even N →
      60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
        (1 / 2 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := by
  have hlog : Real.log =o[Filter.atTop] (fun x : ℝ => x ^ (1 / 20 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)
  have hlogN : (fun n : ℕ => Real.log (n : ℝ)) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 20 : ℝ)) :=
    hlog.comp_tendsto tendsto_natCast_atTop_atTop
  have hN0ev : ∀ᶠ n : ℕ in Filter.atTop,
      |Real.log (n : ℝ)| ≤ (1 / 16 : ℝ) * |(n : ℝ) ^ (1 / 20 : ℝ)| :=
    (Asymptotics.isLittleO_iff.mp hlogN) (by norm_num : 0 < (1 / 16 : ℝ))
  rcases Filter.eventually_atTop.mp hN0ev with ⟨N₀, hN₀⟩
  refine ⟨max (max N₀ 1) 59049, ?_⟩
  intro N hN hEven
  have hN₀' : N₀ ≤ N := by
    omega
  have hN1 : 1 ≤ N := by
    omega
  have hN59049 : 59049 ≤ N := by
    omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN' : Real.log (N : ℝ) ≤ (1 / 16 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ) := by
    have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hx1
    have hpow0 : 0 ≤ (N : ℝ) ^ (1 / 20 : ℝ) :=
      Real.rpow_nonneg (le_of_lt hNpos) _
    have hN₀abs := hN₀ N hN₀'
    have hlogabs : |Real.log (N : ℝ)| = Real.log (N : ℝ) := abs_of_nonneg hlog0
    have hpowabs : |(N : ℝ) ^ (1 / 20 : ℝ)| = (N : ℝ) ^ (1 / 20 : ℝ) := abs_of_nonneg hpow0
    rwa [hlogabs, hpowabs] at hN₀abs
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ (1 / 256 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    have hsq' : (Real.log (N : ℝ)) ^ 2 ≤ ((1 / 16 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 :=
      by simpa [pow_two] using mul_self_le_mul_self hlog0 hlogN'
    calc
      (Real.log (N : ℝ)) ^ 2 ≤ ((1 / 16 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := hsq'
      _ = (1 / 256 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := by
            rw [mul_pow]
            have hpow : ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 = (N : ℝ) ^ (1 / 10 : ℝ) := by
              rw [pow_two]
              rw [← Real.rpow_add hNpos]
              norm_num
            rw [hpow]
            norm_num
  have hgrowth : 240 * (Real.log (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    nlinarith [hsq]
  have hlogsq : (Real.log (N : ℝ)) ^ 2 ≤ (1 / 240 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have h240 : 0 < (240 : ℝ) := by norm_num
    have hgrowth' : (Real.log (N : ℝ)) ^ 2 * 240 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
      simpa [mul_comm] using hgrowth
    have hdiv : (Real.log (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ (1 / 10 : ℝ) / 240 := by
      rw [le_div_iff₀ h240]
      exact hgrowth'
    simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv
  have hpow910 : (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hmul : 60 * (N : ℝ) ^ (9 / 10 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
      (1 / 4 : ℝ) * (N : ℝ) := by
    calc
      60 * (N : ℝ) ^ (9 / 10 : ℝ) * (Real.log (N : ℝ)) ^ 2
          ≤ 60 * (N : ℝ) ^ (9 / 10 : ℝ) * ((1 / 240 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ)) := by
              gcongr
      _ = (1 / 4 : ℝ) * (N : ℝ) := by
            calc
              60 * (N : ℝ) ^ (9 / 10 : ℝ) * ((1 / 240 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ))
                  = (60 * (1 / 240 : ℝ)) * ((N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ)) := by ring
              _ = (1 / 4 : ℝ) * (N : ℝ) := by rw [hpow910]; ring
  have hmain : 60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
      (1 / 4 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    exact (le_div_iff₀ (by positivity : 0 < (Real.log (N : ℝ)) ^ 2)).mpr hmul
  let 𝔖 : ℝ := AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
  have hz : 2 ≤ correctedChenZ N - 1 := correctedChenZ_sub_one_ge_two_of_large hN59049
  have h𝔖 : (1 / 2 : ℝ) ≤ 𝔖 := singularSeriesTruncated_ge_half hz
  have hX0 : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by positivity
  have hfinal : (1 / 4 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      (1 / 2 : ℝ) * 𝔖 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    have hcoef : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) * 𝔖 := by nlinarith [h𝔖]
    have hprod : (1 / 4 : ℝ) * (N : ℝ) ≤ (1 / 2 : ℝ) * 𝔖 * (N : ℝ) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (N : ℝ))
    exact div_le_div_of_nonneg_right hprod (by positivity : 0 ≤ (Real.log (N : ℝ)) ^ 2)
  exact le_trans hmain hfinal

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

/-- The complete Chen Lemma 9 analytic producer followed by the proved
source-to-valuation correction.  Its only inputs are the base lower sieve and
the varying-`q` aggregate upper sieve. -/
theorem chenJurkatRichertWeightedLowerBound_of_asymptotics
    (hbase : ChenJurkatRichertBaseLowerSieveAsymptotic)
    (hupper : ChenJurkatRichertVaryingQUpperSieveStandardInput) :
    ChenJurkatRichertWeightedLowerBound :=
  chenJurkatRichertWeightedLowerBound_of_distinct
    (chenJurkatRichertDistinctWeightedLowerBound_of_asymptotics hbase hupper)

/-- Chen's weighted lower bound directly from the four remaining
Jurkat--Richert literature inputs.  The broader base and varying-`q` asymptotic
predicates remain available as derived APIs, but are not assumptions here. -/
theorem chenJurkatRichertWeightedLowerBound_of_literature_inputs
    (hLowerDensity : DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV : BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperDensity : DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBV : ChenJurkatRichertVaryingQWeightedBombieriVinogradov) :
    ChenJurkatRichertWeightedLowerBound :=
  chenJurkatRichertWeightedLowerBound_of_asymptotics
    (chenJurkatRichertBaseLowerSieveAsymptotic_of_literature_inputs
      hLowerDensity hBV)
    ⟨hUpperDensity, hWeightedBV⟩

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

/-- Prime-AP base count for q¹: `#{p < N : p prime, 2 ≤ N-p, p ≡ N [MOD m]}`. -/
noncomputable def q1APBaseCount (N m : ℕ) : ℕ :=
  ((Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD m])).card

/-- Parity-corrected main term: for even moduli `m`, the AP base count contains only `p = 2`
when `m | N-2`, so use its exact value; for odd moduli use `li(N)/φ(m)`. -/
noncomputable def q1APMainValue (N m : ℕ) : ℝ :=
  if Even m then
    if m ∣ N - 2 then 1 else 0
  else
    AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ) / Nat.totient m

/-- q¹ prime-AP error: base count minus main term; zero for even moduli, by `q1APError_even_zero`. -/
noncomputable def q1APError (N m : ℕ) : ℝ :=
  (q1APBaseCount N m : ℝ) - q1APMainValue N m

/-- Candidate AP count: `#{p ∈ candidates : q | N-p}`. -/
noncomputable def q1CandidateAPCount (N q : ℕ) : ℝ :=
  (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ)

/-- Double Möbius expansion of the candidate AP count in terms of base counts. -/
noncomputable def q1CandidateAPDoubleSum (N q : ℕ) : ℝ :=
  ∑ d ∈ (correctedChenSiftingProduct N).divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
          (q1APBaseCount N (Nat.lcm (Nat.lcm q d) e) : ℝ))

/-- Main term of the candidate AP count, with signed Möbius weights. -/
noncomputable def q1CandidateAPMain (N q : ℕ) : ℝ :=
  ∑ d ∈ (correctedChenSiftingProduct N).divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
          q1APMainValue N (Nat.lcm (Nat.lcm q d) e))

/-- Signed error sum of the candidate AP count. -/
noncomputable def q1CandidateAPErrorSigned (N q : ℕ) : ℝ :=
  ∑ d ∈ (correctedChenSiftingProduct N).divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
          q1APError N (Nat.lcm (Nat.lcm q d) e))

/-- Error bound for the candidate AP count, with absolute Möbius weights. -/
noncomputable def q1CandidateAPError (N q : ℕ) : ℝ :=
  ∑ d ∈ (correctedChenSiftingProduct N).divisors,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        |((ArithmeticFunction.moebius e : ℤ) : ℝ)| * |q1APError N (Nat.lcm (Nat.lcm q d) e)|)

/-- Total q¹ main term: `Σ_{q ∈ [z,y), q prime} q1CandidateAPMain N q`. -/
noncomputable def q1MainTermSum (N : ℕ) : ℝ :=
  ∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
    q1CandidateAPMain N q

/-- Total q¹ error: `Σ_{q ∈ [z,y), q prime} q1CandidateAPError N q`. -/
noncomputable def q1ErrorTermSum (N : ℕ) : ℝ :=
  ∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
    q1CandidateAPError N q

/-- **Möbius coprimality indicator for the sifting product**: `Σ_{d | P_sift, d | m} μ(d) =
1_{∀ prime r | P_sift: ¬ r | m}`. -/
theorem moebius_coprime_sum_sifting (N m : ℕ) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors, if d ∣ m then (μ d : ℝ) else 0) =
      if ∀ r : ℕ, r.Prime → r ∣ correctedChenSiftingProduct N → ¬ r ∣ m
        then (1 : ℝ) else 0 := by
  let P : ℕ := correctedChenSiftingProduct N
  have hdiv : P.divisors.filter (fun d => d ∣ m) = (Nat.gcd m P).divisors := by
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at hd
      rw [Nat.mem_divisors] at hd ⊢
      rcases hd with ⟨hdP, hdm⟩
      rcases hdP with ⟨hdd, hP0⟩
      constructor
      · exact Nat.dvd_gcd_iff.mpr ⟨hdm, hdd⟩
      · have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
        exact ne_of_gt (Nat.gcd_pos_of_pos_right m hPpos)
    · intro hd
      rw [Nat.mem_divisors] at hd
      rw [Finset.mem_filter] at ⊢
      rw [Nat.mem_divisors] at ⊢
      rcases hd with ⟨hg, hg0⟩
      rcases (Nat.dvd_gcd_iff.mp hg) with ⟨hdm, hdd⟩
      constructor
      · exact ⟨hdd, correctedChenSiftingProduct_ne_zero N⟩
      · exact hdm
  have hsum : (∑ d ∈ P.divisors, if d ∣ m then (μ d : ℝ) else 0) =
      (∑ d ∈ (Nat.gcd m P).divisors, (μ d : ℝ)) := by
    rw [← Finset.sum_filter]
    rw [hdiv]
  have hsum' : (∑ d ∈ (Nat.gcd m P).divisors, (μ d : ℝ)) =
      if Nat.gcd m P = 1 then (1 : ℝ) else 0 := by
    have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
    have hkey : (ζ * (μ : ArithmeticFunction ℝ)) (Nat.gcd m P) =
        (1 : ArithmeticFunction ℝ) (Nat.gcd m P) := by rw [h]
    rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
    simpa [ArithmeticFunction.intCoe_apply, mul_comm] using hkey
  have hgcd : (Nat.gcd m P = 1) ↔ ∀ r : ℕ, r.Prime → r ∣ P → ¬ r ∣ m := by
    constructor
    · intro hg r hr hrP hm
      have hrg : r ∣ Nat.gcd m P := Nat.dvd_gcd_iff.mpr ⟨hm, hrP⟩
      rw [hg] at hrg
      have hr1 : r ≤ 1 := Nat.le_of_dvd (by norm_num) hrg
      have hr2 : 2 ≤ r := hr.two_le
      omega
    · intro hcop
      by_contra hg
      have hgne : Nat.gcd m P ≠ 1 := by omega
      obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hgne
      have hrm : r ∣ m := (Nat.dvd_gcd_iff.mp hrd).1
      have hrP : r ∣ P := (Nat.dvd_gcd_iff.mp hrd).2
      exact hcop r hrp hrP hrm
  rw [hsum, hsum']
  by_cases hc : Nat.gcd m P = 1
  · rw [if_pos hc]
    rw [if_pos (hgcd.mp hc)]
  · rw [if_neg hc]
    rw [if_neg (mt hgcd.mpr hc)]

/-- Candidates are the unsifted support restricted by coprimality with `P_sift`: `p ∈ candidates`
iff `p ∈ unsifted` and `N-p` has no prime factor dividing `P_sift`. -/
theorem mem_correctedChenCandidates_iff_coprime_sifting (N p : ℕ) :
    p ∈ correctedChenCandidates N ↔
      p ∈ correctedChenUnsiftedPrimeSupport N ∧
        ∀ r : ℕ, r.Prime → r ∣ correctedChenSiftingProduct N → ¬ r ∣ N - p := by
  unfold correctedChenCandidates correctedChenUnsiftedPrimeSupport
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro hp
    rcases hp with ⟨hpN, hbase⟩
    rcases hbase with ⟨hpp, h2, hno⟩
    constructor
    · exact ⟨hpN, ⟨hpp, ⟨h2, fun r hr hlt hcond => hno r hr hlt⟩⟩⟩
    · intro r hr hrP
      have hlt : r < correctedChenZ N := ((prime_dvd_correctedChenSiftingProduct hr).mp hrP).1
      exact hno r hr hlt
  · intro hp
    rcases hp with ⟨huns, hcop⟩
    rcases huns with ⟨hpN, hbase⟩
    rcases hbase with ⟨hpp, h2, hno⟩
    exact ⟨hpN, ⟨hpp, ⟨h2, by
      intro r hr hlt
      by_cases hcond : r ≤ 2 ∨ r ∣ N
      · exact hno r hr hlt hcond
      · have hnot2 : ¬ r ≤ 2 := by intro h; exact hcond (Or.inl h)
        have hnotN : ¬ r ∣ N := by intro h; exact hcond (Or.inr h)
        have hr2 : 2 < r := by omega
        have hrP : r ∣ correctedChenSiftingProduct N :=
          (prime_dvd_correctedChenSiftingProduct hr).mpr ⟨hlt, hr2, hnotN⟩
        exact hcop r hr hrP⟩⟩⟩

/-- lcm merging: `q | N-p` and `d | N-p` iff `lcm q d | N-p`, using congruences for p < N. -/
private lemma dvd_complement_lcm_iff_modEq {N p q d : ℕ} (hp : p < N) :
    (q ∣ N - p ∧ d ∣ N - p) ↔ p ≡ N [MOD Nat.lcm q d] :=
  (Nat.lcm_dvd_iff.symm.trans (AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq hp))

/-- Unsifted membership and lcm congruence merging: `p ∈ unsifted ∧ q|N-p ∧ d|N-p` iff
`p ∈ unsifted ∧ p ≡ N [MOD lcm(q,d)]`. -/
private lemma unsifted_lcm_congr {N p q d : ℕ} (hp : p < N) :
    (p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p) ↔
      (p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD Nat.lcm q d]) := by
  constructor
  · intro h
    exact ⟨h.1, (dvd_complement_lcm_iff_modEq hp).1 ⟨h.2.1, h.2.2⟩⟩
  · intro h
    exact ⟨h.1, (dvd_complement_lcm_iff_modEq hp).2 h.2⟩

/-- lcm congruence merging in the base count: `p ≡ N [MOD m] ∧ e | N-p` iff
`p ≡ N [MOD lcm(m,e)]`, with the conditions that `p` is prime and `2 ≤ N-p`. -/
private lemma baseCount_lcm_congr {N p m e : ℕ} (hp : p < N) :
    (p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD m] ∧ e ∣ N - p) ↔
      (p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm m e]) := by
  constructor
  · intro h
    exact ⟨h.1, ⟨h.2.1,
      (dvd_complement_lcm_iff_modEq hp).1
        ⟨(AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq hp).2 h.2.2.1, h.2.2.2⟩⟩⟩
  · intro h
    have hlcm : Nat.lcm m e ∣ N - p :=
      (AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq hp).2 h.2.2
    have hm : m ∣ N - p := (Nat.lcm_dvd_iff.mp hlcm).1
    have he : e ∣ N - p := (Nat.lcm_dvd_iff.mp hlcm).2
    exact ⟨h.1, ⟨h.2.1, ⟨(AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq hp).1 hm, he⟩⟩⟩

/-- Pointwise indicator identity: `[p ∈ candidates ∧ q | N-p] =
Σ_{d | P_sift} μ(d)·[p ∈ unsifted ∧ q | N−p ∧ d | N−p]`. -/
private theorem candidatesAP_indicator_eq_moebiusSum (N p q : ℕ) (hp : p ∈ Finset.range N) :
    (if p ∈ correctedChenCandidates N ∧ q ∣ N - p then (1 : ℝ) else 0) =
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        if p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p then (μ d : ℝ) else 0 := by
  have hcop := moebius_coprime_sum_sifting N (N - p)
  by_cases hsupp : p ∈ correctedChenCandidates N
  · by_cases hq : q ∣ N - p
    · rw [if_pos ⟨hsupp, hq⟩]
      have huns : p ∈ correctedChenUnsiftedPrimeSupport N :=
        (Iff.mp (mem_correctedChenCandidates_iff_coprime_sifting N p) hsupp).1
      have hcoprime : ∀ r : ℕ, r.Prime → r ∣ correctedChenSiftingProduct N → ¬ r ∣ N - p := by
        rw [mem_correctedChenCandidates_iff_coprime_sifting] at hsupp
        exact hsupp.2
      have hcop1 : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
          if d ∣ N - p then (μ d : ℝ) else 0) = 1 := by
        rw [hcop]
        rw [if_pos hcoprime]
      calc
        (1 : ℝ) = ∑ d ∈ (correctedChenSiftingProduct N).divisors,
            if d ∣ N - p then (μ d : ℝ) else 0 := hcop1.symm
        _ = ∑ d ∈ (correctedChenSiftingProduct N).divisors,
            if p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p then (μ d : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hdvd : d ∣ N - p <;> simp [huns, hq, hdvd]
    · rw [if_neg (by intro h; exact hq h.2)]
      symm
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hdvd : d ∣ N - p
      · have hne : ¬ (p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p) := by
          intro h
          exact hq h.2.1
        simp [hne]
      · simp [hdvd]
  · rw [if_neg (by intro h; exact hsupp h.1)]
    symm
    by_cases huns_p : p ∈ correctedChenUnsiftedPrimeSupport N
    · by_cases hq : q ∣ N - p
      · have hcop0 : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            if d ∣ N - p then (μ d : ℝ) else 0) = 0 := by
          rw [hcop]
          rw [if_neg]
          intro hcoprime
          exact hsupp (Iff.mpr (mem_correctedChenCandidates_iff_coprime_sifting N p) ⟨huns_p, hcoprime⟩)
        calc
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
              if p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p then (μ d : ℝ) else 0)
              = ∑ d ∈ (correctedChenSiftingProduct N).divisors,
                  if d ∣ N - p then (μ d : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hdvd : d ∣ N - p <;> simp [huns_p, hq, hdvd]
          _ = 0 := hcop0
      · apply Finset.sum_eq_zero
        intro d hd
        by_cases hdvd : d ∣ N - p
        · have hne : ¬ (p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p) := by
            intro h
            exact hq h.2.1
          simp [hne]
        · simp [hdvd]
    · apply Finset.sum_eq_zero
      intro d hd
      by_cases hdvd : d ∣ N - p
      · have hne : ¬ (p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p) := by
          intro h
          exact huns_p h.1
        simp [hne]
      · simp [hdvd]

/-- **First Möbius decomposition of the candidate AP count**: candidates are the unsifted support
restricted by coprimality with `P_sift`, so `#{p ∈ candidates : q | N-p} =
Σ_{d | P_sift} μ(d)·#{p ∈ unsifted : p ≡ N [MOD lcm(q,d)]}`. -/
theorem candidatesAPCount_eq_unsiftedMoebiusSum (N q : ℕ) :
    (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ) =
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD Nat.lcm q d])).card : ℝ) := by
  have h₁ : (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ) =
      ∑ p ∈ correctedChenCandidates N, if q ∣ N - p then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  have h₂ : (∑ p ∈ correctedChenCandidates N, if q ∣ N - p then (1 : ℝ) else 0) =
      ∑ p ∈ (Finset.range N),
        if p ∈ correctedChenCandidates N ∧ q ∣ N - p then (1 : ℝ) else 0 := by
    have hsub : correctedChenCandidates N ⊆ Finset.range N := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    have hz : ∀ p ∈ Finset.range N, p ∉ correctedChenCandidates N →
        (if p ∈ correctedChenCandidates N ∧ q ∣ N - p then (1 : ℝ) else 0) = 0 := by
      intro p hp hnot
      simp [hnot]
    rw [← Finset.sum_subset hsub hz]
    apply Finset.sum_congr rfl
    intro p hp
    simp [hp]
  calc
    (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ)
        = ∑ p ∈ (Finset.range N),
            if p ∈ correctedChenCandidates N ∧ q ∣ N - p then (1 : ℝ) else 0 := h₁.trans h₂
    _ = ∑ p ∈ (Finset.range N),
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            if p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p then (μ d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact candidatesAP_indicator_eq_moebiusSum N p q hp
    _ = ∑ d ∈ (correctedChenSiftingProduct N).divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD Nat.lcm q d])).card : ℝ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          calc
            (∑ p ∈ (Finset.range N),
                if p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p then (μ d : ℝ) else 0)
                = ∑ p ∈ (Finset.range N),
                    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                      (if p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p then (1 : ℝ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    by_cases h : p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p <;> simp [h]
            _ = ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                    (∑ p ∈ (Finset.range N),
                      if p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p then (1 : ℝ) else 0) := by
                    rw [← Finset.mul_sum]
            _ = ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                    (∑ p ∈ (Finset.range N),
                      if p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD Nat.lcm q d] then (1 : ℝ) else 0) := by
                    apply congrArg (fun x => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * x)
                    apply Finset.sum_congr rfl
                    intro p hp
                    have hlt : p < N := Finset.mem_range.mp hp
                    by_cases h : p ∈ correctedChenUnsiftedPrimeSupport N ∧ q ∣ N - p ∧ d ∣ N - p
                    · have hcong : p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD Nat.lcm q d] :=
                        (unsifted_lcm_congr (N := N) (p := p) (q := q) (d := d) hlt).1 h
                      simp [h, hcong]
                    · have hcong : ¬ (p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD Nat.lcm q d]) := by
                        intro hc
                        exact h ((unsifted_lcm_congr (N := N) (p := p) (q := q) (d := d) hlt).2 hc)
                      simp [h, hcong]
            _ = ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                    (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD Nat.lcm q d])).card : ℝ) := by
                    apply congrArg (fun x => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * x)
                    have hsum : (∑ p ∈ (Finset.range N),
                        if p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD Nat.lcm q d] then (1 : ℝ) else 0) =
                        (((Finset.range N).filter (fun p =>
                          p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD Nat.lcm q d])).card : ℝ) := by
                      rw [Finset.sum_boole]
                    rw [hsum]
                    have hf : (Finset.range N).filter (fun p =>
                          p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD Nat.lcm q d]) =
                        (correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD Nat.lcm q d]) := by
                      ext p
                      rw [Finset.mem_filter, Finset.mem_filter]
                      constructor
                      · intro h
                        exact h.2
                      · intro h
                        exact ⟨(Finset.mem_filter.mp h.1).1, h⟩
                    rw [hf]

set_option maxHeartbeats 800000 in
/-- Exact double Möbius expansion of the candidate AP count: `A_q = Σ_{d,e} μ(d)μ(e)·base(lcm(q,d,e))`. -/
theorem q1CandidateAPCount_eq_doubleSum (N q : ℕ) :
    q1CandidateAPCount N q = q1CandidateAPDoubleSum N q := by
  unfold q1CandidateAPCount q1CandidateAPDoubleSum
  calc
    (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ)
        = ∑ d ∈ (correctedChenSiftingProduct N).divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD Nat.lcm q d])).card : ℝ) :=
            candidatesAPCount_eq_unsiftedMoebiusSum N q
    _ = ∑ d ∈ (correctedChenSiftingProduct N).divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
                  (q1APBaseCount N (Nat.lcm (Nat.lcm q d) e) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            apply congrArg (fun x => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * x)
            have hU := unsiftedPrimeSupport_AP_count_eq_moebiusSum N (Nat.lcm q d)
            calc
              (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD Nat.lcm q d])).card : ℝ)
                  = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                      ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
                        (((Finset.range N).filter (fun p =>
                          p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm q d] ∧ e ∣ N - p)).card : ℝ) := hU
              _ = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                      ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
                        (q1APBaseCount N (Nat.lcm (Nat.lcm q d) e) : ℝ) := by
                      apply Finset.sum_congr rfl
                      intro e he
                      apply congrArg (fun x => ((ArithmeticFunction.moebius e : ℤ) : ℝ) * x)
                      unfold q1APBaseCount
                      apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
                      apply Finset.filter_congr
                      intro p hp
                      exact baseCount_lcm_congr (N := N) (m := Nat.lcm q d) (e := e) (Finset.mem_range.mp hp)

/-- For each q, `A_q ≤ main(q) + error(q)`: split each base count as `base = main' + err`
and bound the signed error sum by absolute values. -/
theorem q1CandidateAPCount_le_main_add_error (N q : ℕ) :
    q1CandidateAPCount N q ≤ q1CandidateAPMain N q + q1CandidateAPError N q := by
  have hsplit : ∀ m : ℕ, (q1APBaseCount N m : ℝ) = q1APMainValue N m + q1APError N m := by
    intro m
    unfold q1APError
    ring
  have hsplitSum : q1CandidateAPDoubleSum N q = q1CandidateAPMain N q + q1CandidateAPErrorSigned N q := by
    unfold q1CandidateAPDoubleSum q1CandidateAPMain q1CandidateAPErrorSigned
    simp_rw [hsplit]
    simp [mul_add, Finset.sum_add_distrib]
  have hAbs : ∀ d e : ℕ,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
        q1APError N (Nat.lcm (Nat.lcm q d) e)| =
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (|((ArithmeticFunction.moebius e : ℤ) : ℝ)| * |q1APError N (Nat.lcm (Nat.lcm q d) e)|) := by
    intro d e
    rw [abs_mul, abs_mul]
    ring
  have hErrSigned_le : q1CandidateAPErrorSigned N q ≤ q1CandidateAPError N q := by
    unfold q1CandidateAPErrorSigned q1CandidateAPError
    calc
      (∑ d ∈ (correctedChenSiftingProduct N).divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              ((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e)))
          ≤ ∑ d ∈ (correctedChenSiftingProduct N).divisors,
              ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                |((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
                  q1APError N (Nat.lcm (Nat.lcm q d) e)| := by
            apply Finset.sum_le_sum
            intro d hd
            have hle1 : ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                  ((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e)) ≤
                |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                  (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                    ((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e))| :=
                le_abs_self _
            have hle2 : |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                  ((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e))| ≤
                ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                  |((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
                    q1APError N (Nat.lcm (Nat.lcm q d) e)| := by
                calc
                  |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                        ((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e))|
                      = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                          |∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                            ((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e)| := by
                          rw [abs_mul]
                  _ ≤ |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                          (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                            |((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e)|) := by
                          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
                  _ = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                          |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                            |((ArithmeticFunction.moebius e : ℤ) : ℝ) * q1APError N (Nat.lcm (Nat.lcm q d) e)| := by
                          rw [Finset.mul_sum]
                  _ = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                          |((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
                            q1APError N (Nat.lcm (Nat.lcm q d) e)| := by
                          apply Finset.sum_congr rfl
                          intro e he
                          rw [abs_mul]
                          exact (hAbs d e).symm
            exact le_trans hle1 hle2
      _ = q1CandidateAPError N q := by
            apply Finset.sum_congr rfl
            intro d hd
            symm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            exact (hAbs d e).symm
  have hMainAdd : q1CandidateAPMain N q + q1CandidateAPErrorSigned N q ≤
      q1CandidateAPMain N q + q1CandidateAPError N q := by
    nlinarith [hErrSigned_le]
  exact ((q1CandidateAPCount_eq_doubleSum N q).trans hsplitSum).trans_le hMainAdd

/-- **Finite q¹ reduction**: `q1Count ≤ q1MainTermSum + q1ErrorTermSum`, by exact algebra
(reindexing, double Möbius expansion, and splitting the base counts). -/
theorem q1Count_le_mainTerm_add_error (N : ℕ) :
    correctedChenQ1Count N ≤ q1MainTermSum N + q1ErrorTermSum N := by
  rw [correctedChenQ1Count_eq_reindexed]
  unfold q1MainTermSum q1ErrorTermSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  exact q1CandidateAPCount_le_main_add_error N q

/-- For even moduli, the AP base count contains only `p = 2`: for even `N ≥ 4` and even `m`,
`q1APBaseCount N m = 1` if `m | N-2`, and is zero otherwise. -/
theorem q1APBaseCount_even (N m : ℕ) (hN : Even N) (hN4 : 4 ≤ N) (hm : Even m) :
    q1APBaseCount N m = if m ∣ N - 2 then 1 else 0 := by
  unfold q1APBaseCount
  by_cases hdvd : m ∣ N - 2
  · have hfilter : ((Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD m])) = {2} := by
      ext p
      constructor
      · intro hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        rcases hp with ⟨hpN, hbase⟩
        rcases hbase with ⟨hpp, h2, hcong⟩
        have hm2 : 2 ∣ m := by rcases hm with ⟨k, hk⟩; refine ⟨k, ?_⟩; omega
        have hmdvd : m ∣ N - p := (Nat.modEq_iff_dvd' (by omega : p ≤ N)).1 hcong
        have h2dvd : 2 ∣ N - p := dvd_trans hm2 hmdvd
        have hpeven : Even p := by
          rcases hN with ⟨a, ha⟩
          rcases h2dvd with ⟨b, hb⟩
          use a - b
          omega
        have hp2' : p = 2 := by
          rcases hpp.eq_two_or_odd' with h2 | hod
          · exact h2
          · exfalso
            rcases hpeven with ⟨c, hc⟩
            rcases hod with ⟨d, hd⟩
            omega
        subst p
        rw [Finset.mem_singleton]
      · intro hp
        rw [Finset.mem_singleton] at hp
        subst p
        rw [Finset.mem_filter, Finset.mem_range]
        constructor
        · omega
        · exact ⟨by norm_num, by omega, (Nat.modEq_iff_dvd' (n := m) (a := 2) (b := N) (by omega : 2 ≤ N)).2 hdvd⟩
    rw [hfilter]
    simp [hdvd]
  · have hfilter : ((Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD m])) = ∅ := by
      ext p
      constructor
      · intro hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        rcases hp with ⟨hpN, hbase⟩
        rcases hbase with ⟨hpp, h2, hcong⟩
        have hm2 : 2 ∣ m := by rcases hm with ⟨k, hk⟩; refine ⟨k, ?_⟩; omega
        have hmdvd : m ∣ N - p := (Nat.modEq_iff_dvd' (by omega : p ≤ N)).1 hcong
        have h2dvd : 2 ∣ N - p := dvd_trans hm2 hmdvd
        have hpeven : Even p := by
          rcases hN with ⟨a, ha⟩
          rcases h2dvd with ⟨b, hb⟩
          use a - b
          omega
        have hp2' : p = 2 := by
          rcases hpp.eq_two_or_odd' with h2 | hod
          · exact h2
          · exfalso
            rcases hpeven with ⟨c, hc⟩
            rcases hod with ⟨d, hd⟩
            omega
        subst p
        exact False.elim (hdvd ((Nat.modEq_iff_dvd' (n := m) (a := 2) (b := N) (by omega : 2 ≤ N)).1 (by simpa using hcong)))
      · intro h
        simp at h
    rw [hfilter]
    simp [hdvd]

/-- The q¹ error vanishes for even moduli because `q1APMainValue` uses their exact count. -/
theorem q1APError_even_zero {N m : ℕ} (hN : Even N) (hN4 : 4 ≤ N) (hm : Even m) :
    q1APError N m = 0 := by
  unfold q1APError
  rw [q1APBaseCount_even N m hN hN4 hm]
  unfold q1APMainValue
  by_cases hdvd : m ∣ N - 2 <;> simp [hm, hdvd]

/-- **q¹ main-term absorption**, an analytic input:
`Σ_{q ∈ [z,y)} q1CandidateAPMain N q ≤ C₁·𝔖_trunc·N/log²N`.

The main-term structure, from the exact Möbius decomposition `q1CandidateAPCount_eq_doubleSum`, is
`q1CandidateAPMain N q = li(N)/φ(q)·∏_{2<r<z}(1-1/(r-1)) + O(parity correction)`,
where `li(N) = N/log N`. The product is absorbed using the local-factor structure of `singularSeriesTruncated`
and `primeReciprocalSum_range_le`, the Mertens-type range bound for prime reciprocals,
into `C₁·𝔖_trunc·N/log²N`. This logarithmic absorption is an analytic step and remains an explicit
input to the conditional argument; it requires the prime-reciprocal bound and the singular-series product structure. -/
def q1MainTermAbsorption : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → Even N →
    q1MainTermSum N ≤
      C₁ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        (N : ℝ) / (log (N : ℝ)) ^ 2

/-- **Uniform q¹ error bound**, an analytic output required of a weighted aggregate theorem:
`Σ_{q ∈ [z,y)} q1CandidateAPError N q ≤ C₂·N/log³N`.

`q1CandidateAPError` is the double Möbius error sum `Σ_q Σ_{d,e} |μ(d)μ(e)|·|err(lcm(q,d,e))|`,
where `err(m) = π'(N;m) - main term`. The parity correction in `q1APMainValue` makes it exactly zero
for even moduli; see `q1APError_even_zero`. The classical Pan theorem gives a
`μ²(m)3^{ω(m)}`-weighted average only for `m ≤ N^{1/2}/log(N)^B`. This definition retains
all divisors `d | P_sift` and `e | P_forb`, so `lcm(q,d,e)` has no such modulus upper bound.
This all-positive error interface is retained only for the finite algebraic audit. The canonical route in
`Q1LevelSupportedSieve` first bounds q¹ counts with finite-level Selberg squares, then passes reduced moduli
within the cutoff to the weighted Pan/BV input; it no longer uses this definition. -/
def q1APErrorUniformBound : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → Even N →
    q1ErrorTermSum N ≤ C₂ * (N : ℝ) / (log (N : ℝ)) ^ 3

/-- **Conditional hq1 theorem**: assume main-term absorption
`q1MainTermAbsorption` and the aggregate error bound `q1APErrorUniformBound`.
The latter is the required Pan-bridge output, not a consequence of `PanMeanValueUniform` without further truncation control.
Then the q¹ count has a uniform bound `∃ Cq Nq: q1Count(N) ≤ Cq·𝔖_trunc·N/log²N`,
exactly the `hq1` input of `corrected_chens_theorem_of_q1Count_and_triple`.

Assembly: `q1Count ≤ Main + Error` by `q1Count_le_mainTerm_add_error`;
the main term is ≤ `C₁·𝔖·X`, and the error is ≤ `C₂·N/log³N` ≤ `(1/4)·N/log²N`
(`errLogCube_negligible`) ≤ `(1/2)·𝔖·X` (`𝔖 ≥ 1/2`,
`singularSeriesTruncated_ge_half`), so `Cq = C₁ + 1/2`. -/
theorem hq1_of_q1AnalyticInputs
    (hMain : q1MainTermAbsorption) (hErr : q1APErrorUniformBound) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∃ Nq : ℕ, ∀ N : ℕ, Nq ≤ N → Even N →
      correctedChenQ1Count N ≤ Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
  rcases hMain with ⟨C₁, hC₁, N₁, hMain'⟩
  rcases hErr with ⟨C₂, hC₂, N₂, hErr'⟩
  rcases errLogCube_negligible C₂ with ⟨N₀, hN₀⟩
  refine ⟨C₁ + 1 / 2, by positivity, max (max N₁ (max N₂ N₀)) 59049, ?_⟩
  intro N hN hEven
  have hN₁ : N₁ ≤ N := by omega
  have hN₂ : N₂ ≤ N := by omega
  have hN₀' : N₀ ≤ N := by omega
  have hN59049 : 59049 ≤ N := by omega
  let 𝔖 : ℝ := AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
  let X : ℝ := (N : ℝ) / (log (N : ℝ)) ^ 2
  have hred := q1Count_le_mainTerm_add_error N
  have hMainN : q1MainTermSum N ≤ C₁ * 𝔖 * X := by
    rw [show C₁ * 𝔖 * X =
        C₁ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 by ring]
    exact hMain' N hN₁ hEven
  have hErrN : q1ErrorTermSum N ≤ C₂ * (N : ℝ) / (log (N : ℝ)) ^ 3 := hErr' N hN₂ hEven
  have hErrCube : C₂ * (N : ℝ) / (log (N : ℝ)) ^ 3 ≤
      (1 / 4 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2 := hN₀ N hN₀' hEven
  have h𝔖 : (1 / 2 : ℝ) ≤ 𝔖 := by
    dsimp [𝔖]
    exact singularSeriesTruncated_ge_half (correctedChenZ_sub_one_ge_two_of_large hN59049)
  have hErrAbsorb : (1 / 4 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2 ≤ (1 / 2 : ℝ) * 𝔖 * X := by
    have hcoef : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) * 𝔖 := by nlinarith [h𝔖]
    dsimp [X]
    calc
      (1 / 4 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2
          = (1 / 4 : ℝ) * ((N : ℝ) / (log (N : ℝ)) ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * 𝔖 * ((N : ℝ) / (log (N : ℝ)) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hq1' : correctedChenQ1Count N ≤ (C₁ + 1 / 2) * 𝔖 * X := by
    calc
      correctedChenQ1Count N ≤ q1MainTermSum N + q1ErrorTermSum N := hred
      _ ≤ C₁ * 𝔖 * X + C₂ * (N : ℝ) / (log (N : ℝ)) ^ 3 := add_le_add hMainN hErrN
      _ ≤ C₁ * 𝔖 * X + (1 / 2 : ℝ) * 𝔖 * X := by
            exact add_le_add le_rfl (le_trans hErrCube hErrAbsorb)
      _ = (C₁ + 1 / 2) * 𝔖 * X := by ring
  calc
    correctedChenQ1Count N ≤ (C₁ + 1 / 2) * 𝔖 * X := hq1'
    _ = (C₁ + 1 / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
          dsimp [𝔖, X]
          ring

end MathlibNt.SieveTheory.SwitchingPrinciple
