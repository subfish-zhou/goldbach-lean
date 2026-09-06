import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147JurkatRichertInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenAdaptiveDepthAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDensityBoundingSieveBridge

/-!
# Uniform Suzuki lower density for Chen's varying source family

This is the first production consumer of the uniform-in-sieve Lemma 14.7.  Its
constant is chosen before the varying family
`jurkatRichertSourceBoundingSieve N`; the proof then uses the literal Chen
floor level, adaptive supported-carrier depth, and the exact Euler/main-sum
bridges.  No conclusion-shaped comparison premise is used.
-/

open scoped Classical BigOperators Interval
open Set Filter Topology Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- Increasing the displayed dimension-one constant preserves the local-product
bound.  This lets the source witness, which is stated with `1 < K`, meet the
literal all-depth consumer's harmless normalization `2 ≤ K`. -/
theorem HasDimensionOneLocalProductBound.mono_constant
    {S : BoundingSieve} {K K' : ℝ}
    (h : HasDimensionOneLocalProductBound S K) (hKK' : K ≤ K') :
    HasDimensionOneLocalProductBound S K' := by
  exact MathlibNt.SieveTheory.hasDimensionOneLocalProductBound_mono_K h hKK'

/-- The floor in Chen's level makes the Suzuki cutoff strictly larger even when
a source prime lies exactly at the real tenth-power endpoint. -/
theorem chen_le_tenth_rpow_imp_lt_chenZ
    {N p : ℕ} {ε : ℝ} (hN : 1 ≤ N) (_hε0 : 0 ≤ ε)
    (hε : ε < 1 / 10)
    (hp : (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    p < chenZ N ε := by
  let a : ℝ := 1 / 2 - ε
  let s : ℝ := chenS ε
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNnonneg : 0 ≤ (N : ℝ) := hNpos.le
  have hs : 0 < s := by
    dsimp [s, chenS]
    linarith
  have hfloor : (N : ℝ) ^ a < (chenLevel N ε : ℝ) := by
    simpa [chenLevel, a] using lt_cast_floor_add_one ((N : ℝ) ^ a)
  have hpow : ((N : ℝ) ^ a) ^ (1 / s) <
      (chenLevel N ε : ℝ) ^ (1 / s) :=
    Real.rpow_lt_rpow (Real.rpow_nonneg hNnonneg _) hfloor (by positivity)
  have hid : ((N : ℝ) ^ a) ^ (1 / s) =
      (N : ℝ) ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_mul hNnonneg]
    congr 1
    dsimp [a, s]
    exact chen_exponent_div_s (by linarith)
  rw [hid] at hpow
  rw [chenZ, Nat.lt_ceil]
  exact hp.trans_lt hpow

/-- On Chen's interval, the natural Suzuki cutoff is no larger than the natural
floor level.  This is the missing finite-carrier bridge needed by the exact
`mainSum` theorem. -/
theorem chenZ_le_chenLevel
    {N : ℕ} {ε : ℝ} (hD : 2 ≤ chenLevel N ε)
    (hs : 1 ≤ chenS ε) :
    chenZ N ε ≤ chenLevel N ε := by
  rw [chenZ, Nat.ceil_le]
  apply Real.rpow_le_self_of_one_le
  · exact_mod_cast (show 1 ≤ chenLevel N ε by omega)
  · have hspos : 0 < chenS ε := zero_lt_one.trans_le hs
    exact (div_le_one hspos).2 hs

/-- Chen's varying source family satisfies the eventual lower-density estimate
with one Suzuki constant selected before the family varies.  The fixed source
parameters are exactly `(d, Δ, Θ) = (16, 1/2, 7)`.

The conclusion is at Chen's literal floor level and uses the production lower
Rosser weight.  The arbitrary positive `ρ` absorbs the complete adaptive-depth
Suzuki error uniformly in the growing supported carrier. -/
theorem eventually_jurkatRichertSource_lowerDensity_of_section13HatSource
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {ε ρ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 10) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop,
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
          (jurkatRichertSourceBoundingSieve N) *
          (dimensionOneLowerLinearSieveFactor (chenS ε) - ρ) ≤
        (jurkatRichertSourceBoundingSieve N).mainSum
          (jurkatRichertBaseLowerRosserWeight N ε) := by
  have hsrc : SuzukiClaim145SourceParameters
      (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, hC1min, huniform⟩ :=
    exists_lowerRosserDensity_dimensionOneLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      H hH hsrc
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hall⟩ :=
    huniform C1min le_rfl
  obtain ⟨K₀, hK₀, hlocal₀⟩ :=
    exists_jurkatRichertSource_dimensionOneLocalProductBound
  let K : ℝ := max 2 K₀
  have hK : 2 ≤ K := le_max_left _ _
  have hlocal : ∀ N : ℕ,
      HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) K := by
    intro N
    exact HasDimensionOneLocalProductBound.mono_constant
      (hlocal₀ N) (le_max_right _ _)
  obtain ⟨Nσ, hNσ⟩ := exists_chen_floor_level_sourceSigma_gate
  obtain ⟨NE, hNE⟩ :=
    chen_eventually_all_depth_suzuki_error_absorption
      H hH.toSection13HatContract (le_trans (by norm_num) hC) hε0 hε ρ hρ
  have hDlargeReal : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ chenLevel N ε :=
    (tendsto_chenLevel_atTop hε).eventually (eventually_ge_atTop 2)
  have hDlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ chenLevel N ε :=
    hDlargeReal.mono fun N hN => by exact_mod_cast hN
  have hσ : ∀ᶠ N : ℕ in atTop,
      chenS ε ≤ sourceSigma (chenLevel N ε : ℝ) 16 :=
    eventually_atTop.2 ⟨Nσ, fun N hN => hNσ N hN ε hε0 hε⟩
  have hE : ∀ᶠ N : ℕ in atTop, ∀ depth : ℕ,
      C * Real.exp (Real.sqrt K) *
          errorEnvelope H depth (chenLevel N ε : ℝ) 16 (chenS ε) *
            (Real.log (chenLevel N ε : ℝ)) ^ (-(1 / 2 : ℝ)) < ρ :=
    eventually_atTop.2 ⟨NE, fun N hN => hNE N hN⟩
  filter_upwards [hDlarge, hσ, hE, eventually_ge_atTop 1] with
      N hD hSigma hError hN
  let S : BoundingSieve := jurkatRichertSourceBoundingSieve N
  let D : ℕ := chenLevel N ε
  let s : ℝ := chenS ε
  let z : ℕ := chenZ N ε
  let depth : ℕ := 2 * ((suzukiSupportedBelow S z).card + 1)
  have hs4 : 4 ≤ s := by dsimp [s, chenS]; linarith
  have hs6 : s ≤ 6 := by dsimp [s, chenS]; linarith
  have hs1 : 1 ≤ s := by linarith
  have hzD : z ≤ D := by
    dsimp [z, D, s]
    exact chenZ_le_chenLevel hD hs1
  have hz2 : 2 ≤ z := by
    have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 0 < 1 / s := by positivity
    have hrpow : (1 : ℝ) < (D : ℝ) ^ (1 / s) :=
      Real.one_lt_rpow (by exact_mod_cast (show 1 < D by omega)) hexp
    have hzreal : (1 : ℝ) < (z : ℝ) := by
      dsimp [z, chenZ, D, s]
      exact hrpow.trans_le (Nat.le_ceil _)
    exact_mod_cast hzreal
  have hcutZ : ∀ p ∈ S.prodPrimes.primeFactors, p < z := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ jurkatRichertSourceSiftingProduct N :=
      (Nat.mem_primeFactors_of_ne_zero
        (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp |>.2
    have hpReal := (prime_dvd_jurkatRichertSourceSiftingProduct hpPrime).mp hpDvd |>.2.1
    dsimp [S, z]
    exact chen_le_tenth_rpow_imp_lt_chenZ hN hε0 hε hpReal
  have hcutD : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact (hcutZ p hp).trans_le hzD
  have hdensityRaw := hall S K hK (hlocal N) D (by simpa [D] using hD)
    s (by simpa [s] using hs4) (by simpa [s] using hs6)
    (by simpa [S, D, s] using hSigma) (by simpa [z, D, s, chenZ] using hz2)
  have hdensity :
      suzukiVProduct S (z : ℝ) *
          (dimensionOneLowerLinearSieveFactor s -
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H depth (D : ℝ) 16 s *
                (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
        lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
    simpa [z, chenZ, D, s, depth] using hdensityRaw
  have hbridge := suzukiDensityProduct_lowerRosserWeight_exact_bridge
    S D z hcutZ hcutD
  have hV : 0 ≤ suzukiVProduct S (z : ℝ) :=
    (suzukiVProduct_pos S (z : ℝ)).le
  have hErrorDepth :
      C * Real.exp (Real.sqrt K) *
          errorEnvelope H depth (D : ℝ) 16 s *
            (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ)) < ρ := by
    simpa [depth, S, z, D, s] using hError depth
  have htransport :
      suzukiVProduct S (z : ℝ) *
          (dimensionOneLowerLinearSieveFactor s - ρ) ≤
        suzukiVProduct S (z : ℝ) *
          (dimensionOneLowerLinearSieveFactor s -
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H depth (D : ℝ) 16 s *
                (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hV
    linarith
  have hfinal := htransport.trans hdensity
  rw [← hbridge.1, hbridge.2.1] at hfinal
  change AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
      (dimensionOneLowerLinearSieveFactor s - ρ) ≤
    S.mainSum (lowerRosserWeight S.prodPrimes D)
  exact hfinal

/-- The source-contract-relative Chen/Jurkat--Richert base lower-density
fundamental lemma, obtained directly from the natural-ceiling varying-family
producer rather than through the stronger generic real-parameter comparison. -/
theorem chenJurkatRichertBaseLowerRosserDensityFundamentalLemma_of_section13HatSource
    (H : Section13HatLayers) (hH : Section13HatSourceContract H) :
    ChenJurkatRichertBaseLowerRosserDensityFundamentalLemma := by
  intro _K _hK _hlocal δ hδ
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hnear :
      {s : ℝ | dimensionOneLowerLinearSieveFactor 5 - ρ <
        dimensionOneLowerLinearSieveFactor s} ∈ 𝓝 5 :=
    dimensionOneLowerLinearSieveFactor_continuousAt_five.eventually_mem
      (Ioi_mem_nhds (by linarith))
  rw [Metric.mem_nhds_iff] at hnear
  obtain ⟨r, hr, hrball⟩ := hnear
  let ε : ℝ := min (r / 20) (1 / 20)
  have hε : 0 < ε := lt_min (div_pos hr (by norm_num)) (by norm_num)
  have hεTenth : ε < 1 / 10 := by
    have hle := min_le_right (r / 20) (1 / 20 : ℝ)
    dsimp [ε]
    linarith
  have hεTwoFifths : ε < 2 / 5 := by linarith
  have hεRadius : ε ≤ r / 20 := min_le_left _ _
  have hsNear :
      dimensionOneLowerLinearSieveFactor 5 - ρ <
        dimensionOneLowerLinearSieveFactor (chenS ε) := by
    apply hrball
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |chenS ε - 5| = 10 * ε := by
      unfold chenS
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [habs]
    nlinarith
  refine ⟨ε, hε, hεTwoFifths, ?_⟩
  have hfamily := eventually_jurkatRichertSource_lowerDensity_of_section13HatSource
    H hH hε.le hεTenth hρ
  filter_upwards [hfamily] with N hbound
  have hproduct :
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
  calc
    (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) ≤
        (dimensionOneLowerLinearSieveFactor (chenS ε) - ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) := by
      apply mul_le_mul_of_nonneg_right _ hproduct
      rw [← dimensionOneLowerLinearSieveFactor_five]
      dsimp [ρ] at *
      linarith
    _ ≤ _ := by simpa [mul_comm] using hbound

/-- The exact finite lower-Rosser expansion turns the density theorem above into
Chen's base lower-sieve fundamental lemma, still retaining the genuine finite
Goldbach remainder. -/
theorem chenJurkatRichertBaseLowerSieveFundamentalLemma_of_section13HatSource
    (H : Section13HatLayers) (hH : Section13HatSourceContract H) :
    ChenJurkatRichertBaseLowerSieveFundamentalLemma :=
  chenJurkatRichertBaseLowerSieveFundamentalLemma_of_density
    (chenJurkatRichertBaseLowerRosserDensityFundamentalLemma_of_section13HatSource H hH)

/-- Chen's base lower asymptotic after the Suzuki source contract and the genuine
standard Bombieri--Vinogradov input.  The former now supplies the complete lower
sieve; the only remaining premise here is the named distribution theorem. -/
theorem chenJurkatRichertBaseLowerSieveAsymptotic_of_section13HatSource_and_standardBV
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (hBV : BombieriVinogradov.StandardBombieriVinogradov) :
    ChenJurkatRichertBaseLowerSieveAsymptotic :=
  chenJurkatRichertBaseLowerSieveAsymptotic_of_inputs
    (chenJurkatRichertBaseLowerSieveFundamentalLemma_of_section13HatSource H hH)
    (chenJurkatRichertBaseGoldbachDistribution_of_standardBV hBV)


end MathlibNt.SieveTheory
