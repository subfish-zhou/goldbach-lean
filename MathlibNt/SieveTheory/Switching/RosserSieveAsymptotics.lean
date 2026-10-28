import MathlibNt.SieveTheory.Switching.VaryingPrimeSieve
import MathlibNt.Tactic.ElementaryDeriv
import MathlibNt.SieveTheory.Switching.BoundaryDensity

/-!
# Rosser lower sieves and Mertens normalization

Depth-zero boundary assembly, lower Rosser density inputs, and standard
Bombieri--Vinogradov distribution bounds combine with explicit Mertens and
singular-series normalization to give the base lower-sieve asymptotic.

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


/-- The literal source sieve inherits the real-endpoint dimension-one estimate
from the Goldbach local-factor interval bound. -/
theorem exists_jurkatRichertSource_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ N : ℕ,
      HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N z₁ z₂ hz₁ hz₁₂
  let s : Finset ℕ :=
    (jurkatRichertSourceSiftingProduct N).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' :
        p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ jurkatRichertSourceSiftingProduct N :=
      (Nat.mem_primeFactors_of_ne_zero
        (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp'.1 |>.2
    exact ⟨hprime,
      (prime_dvd_jurkatRichertSourceSiftingProduct hprime).mp hpdiv |>.1⟩
  have hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
    intro p hp
    have hp' :
        p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    exact hp'.2
  have hbound := hinterval s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := hbound


/-- The generic lower factor at ratio five is exactly Chen's equation (26)
factor. -/
theorem dimensionOneLowerLinearSieveFactor_five :
    dimensionOneLowerLinearSieveFactor 5 =
      jurkatRichertBaseSieveFactor jurkatRichertJ := by
  unfold dimensionOneLowerLinearSieveFactor jurkatRichertBaseSieveFactor
    jurkatRichertJ
  norm_num

/-- Compatibility form of the lower density lemma specialized to Chen's source
family.  It is derived below from the generic dimension-one theorem. -/
def ChenJurkatRichertBaseLowerRosserDensityFundamentalLemma : Prop :=
  ∀ K : ℝ, 1 < K →
    (∀ᶠ N : ℕ in Filter.atTop,
      HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) K) →
    ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < 2 / 5 ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
              AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                (jurkatRichertSourceBoundingSieve N) ≤
            (jurkatRichertSourceBoundingSieve N).mainSum
              (jurkatRichertBaseLowerRosserWeight N ε)


/-- The remaining standard source input is precisely the density-sum fundamental
lemma, since the local-product condition is now proved above. -/
def ChenJurkatRichertBaseLowerRosserStandardInput : Prop :=
  ChenJurkatRichertBaseLowerRosserDensityFundamentalLemma

/-- The source-faithful lower-sieve fundamental lemma at
`D = N^(1/2-ε)`.  It retains the exact finite Goldbach remainder rather than
folding distribution or Mertens normalization into the conclusion. -/
def ChenJurkatRichertBaseLowerSieveFundamentalLemma : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
              ((jurkatRichertSourceBoundingSieve N).totalMass *
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                  (jurkatRichertSourceBoundingSieve N)) -
            jurkatRichertSourceRemainderSum N ε ≤
          (jurkatRichertSourceBoundingSieve N).siftedSum

/-- The source Rosser coefficient is a finite lower-Möbius weight at its stated
level.  This is the combinatorial half of the fundamental lemma. -/
theorem jurkatRichertBaseLowerRosserWeight_certificate
    {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : ε < 2 / 5) :
    LinearSieve.IsLowerRosserCertificate
      (jurkatRichertSourceSiftingProduct N)
      (jurkatRichertSourceLowerLevel N ε) := by
  apply LinearSieve.lowerRosserWeight_certificate
    (jurkatRichertSourceSiftingProduct_squarefree N)
    (jurkatRichertSourceSiftingProduct_ne_zero N)
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ jurkatRichertSourceSiftingProduct N :=
    (Nat.mem_primeFactors_of_ne_zero
      (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp |>.2
  have hpCutoff :=
    (prime_dvd_jurkatRichertSourceSiftingProduct hpPrime).mp hpDvd |>.2.1
  have hpow :
      (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hN
    · linarith
  have hpFloor :
      p ≤ Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) := by
    rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
    exact hpCutoff.trans hpow
  unfold jurkatRichertSourceLowerLevel
  omega

/-- The Rosser error term is bounded by exactly the level-restricted Goldbach
remainder appearing in the source statement. -/
theorem jurkatRichertBaseLowerRosserError_le
    (N : ℕ) (ε : ℝ) :
    LinearSieve.lowerErrSum (jurkatRichertSourceBoundingSieve N)
        (jurkatRichertSourceLowerLevel N ε)
        (jurkatRichertBaseLowerRosserWeight N ε) ≤
      jurkatRichertSourceRemainderSum N ε := by
  have hfilter :
      (jurkatRichertSourceSiftingProduct N).divisors.filter
          (fun d => d < jurkatRichertSourceLowerLevel N ε) =
        (jurkatRichertSourceSiftingProduct N).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε)) := by
    ext d
    simp only [Finset.mem_filter]
    unfold jurkatRichertSourceLowerLevel
    rw [Nat.lt_succ_iff, Nat.le_floor_iff
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  unfold LinearSieve.lowerErrSum jurkatRichertSourceRemainderSum
  change
    (∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d => d < jurkatRichertSourceLowerLevel N ε),
      |jurkatRichertBaseLowerRosserWeight N ε d| *
        |(jurkatRichertSourceBoundingSieve N).rem d|) ≤
      ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε)),
        |(jurkatRichertSourceBoundingSieve N).rem d|
  rw [hfilter]
  apply Finset.sum_le_sum
  intro d hd
  have hbnd :=
    LinearSieve.abs_lowerRosserWeight_le_one
      (jurkatRichertSourceSiftingProduct N)
      (jurkatRichertSourceLowerLevel N ε) d
  simpa [jurkatRichertBaseLowerRosserWeight] using
    mul_le_mul_of_nonneg_right hbnd
      (abs_nonneg ((jurkatRichertSourceBoundingSieve N).rem d))

/-- The standard density-sum fundamental lemma, together with the fully finite
Rosser expansion above, proves Chen's base lower-sieve statement. -/
theorem chenJurkatRichertBaseLowerSieveFundamentalLemma_of_density
    (hinput : ChenJurkatRichertBaseLowerRosserStandardInput) :
    ChenJurkatRichertBaseLowerSieveFundamentalLemma := by
  obtain ⟨K, hK, hdimension⟩ :=
    exists_jurkatRichertSource_dimensionOneLocalProductBound
  intro δ hδ
  rcases hinput K hK (Filter.Eventually.of_forall hdimension) δ hδ with
    ⟨ε, hε, hεTwoFifths, hdensity⟩
  refine ⟨ε, hε, by linarith, ?_⟩
  filter_upwards [hdensity, Filter.eventually_ge_atTop 2] with N hdensityN hN
  intro _hEven
  let S := jurkatRichertSourceBoundingSieve N
  let D := jurkatRichertSourceLowerLevel N ε
  let mu := jurkatRichertBaseLowerRosserWeight N ε
  have hcert : LinearSieve.IsLowerRosserCertificate
      (jurkatRichertSourceSiftingProduct N) D := by
    simpa [D] using
      jurkatRichertBaseLowerRosserWeight_certificate (by omega) hεTwoFifths
  have hfinite :
      S.totalMass * S.mainSum mu - LinearSieve.lowerErrSum S D mu ≤
        S.siftedSum := by
    exact LinearSieve.mainSum_sub_lowerErrSum_le_siftedSum D mu hcert
      (LinearSieve.lowerRosserWeight_hasLowerLevelSupport
        (jurkatRichertSourceSiftingProduct N) D)
  have hmass : 0 ≤ S.totalMass := by
    dsimp [S, jurkatRichertSourceBoundingSieve]
    exact LiuWeight.liuLogarithmicIntegral_nonneg
      (2 / Real.log 2) (by positivity) (by exact_mod_cast hN)
  have hmain :
      S.totalMass *
          ((jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) ≤
        S.totalMass * S.mainSum mu :=
    mul_le_mul_of_nonneg_left (by simpa [S, mu] using hdensityN) hmass
  have herr :
      LinearSieve.lowerErrSum S D mu ≤
        jurkatRichertSourceRemainderSum N ε := by
    simpa [S, D, mu] using jurkatRichertBaseLowerRosserError_le N ε
  calc
    (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
            (S.totalMass *
             AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) -
          jurkatRichertSourceRemainderSum N ε ≤
        S.totalMass * S.mainSum mu - LinearSieve.lowerErrSum S D mu := by
      nlinarith
    _ ≤ S.siftedSum := hfinite

/-- The Goldbach AP distribution input required by the base lower sieve:
the exact squarefree remainder sum through `N^(1/2-ε)` is negligible on the
`𝔖(N) N / log² N` scale. -/
def ChenJurkatRichertBaseGoldbachDistribution : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      jurkatRichertSourceRemainderSum N ε ≤
        δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ)

/-- The standard Bombieri--Vinogradov literature interface supplies precisely
the base Goldbach distribution estimate needed by the source lower sieve.  The
proof retains the finite source support, reduces its moduli to canonical
reduced residues, and absorbs the exceptional cutoff-prime fibres by their
unconditional power-saving endpoint bound. -/
theorem chenJurkatRichertBaseGoldbachDistribution_of_standardBV
    (hBV : BombieriVinogradov.StandardBombieriVinogradov) :
    ChenJurkatRichertBaseGoldbachDistribution := by
  intro ε hε hεHalf δ hδ
  rcases BombieriVinogradov.endpoint_bound hBV 3 (by norm_num) with
    ⟨B, hB, C, hC, hBV⟩
  let U := SingularSeries.liuUniversalProduct
  have hU : 0 < U := by
    simpa [U] using SingularSeries.liuUniversalProduct_pos
  let cerr := 4 * C / (δ * U)
  obtain ⟨N₀, hcerr⟩ := errLogCube_negligible cerr
  have hcut :=
    LiuWeight.eventually_liuSourceDEpsilon_le_panModulusCutoff ε B hε hB
  have hendpoint :=
    eventually_jurkatRichertSource_exceptional_endpoint_small ε (δ / 2)
      hε (by linarith)
  filter_upwards [hBV, hcut, hendpoint,
      Filter.eventually_ge_atTop (max N₀ 3)] with N hBVN hcutN hendpointN hN
  intro hEven
  have hN₂ : 2 ≤ N := by omega
  have hNgt : 2 < N := by omega
  let D := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))
  let E := jurkatRichertSourceExceptionalPrimes N
  let Q := Finset.Icc 1 (LiuWeight.panModulusCutoff N B)
  have hDsub : D ⊆ Q := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdDiv, hdLevel⟩
    have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
      Nat.dvd_of_mem_divisors hdDiv
    have hd0 : d ≠ 0 := by
      intro hd0
      subst d
      have hP0 : jurkatRichertSourceSiftingProduct N = 0 := by simpa using hdvd
      exact jurkatRichertSourceSiftingProduct_ne_zero N hP0
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr hd0
    · have hdFloor : d ≤ LiuWeight.liuSourceDEpsilon N ε := by
        exact Nat.le_floor hdLevel
      exact hdFloor.trans hcutN
  have hmaxSum :
      (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
        ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q :=
    Finset.sum_le_sum_of_subset_of_nonneg hDsub
      (fun q _ _ => BombieriVinogradov.standardPrimeAPMaxError_nonneg N q)
  have hBVsum :
      (∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q) ≤
        C * (N : ℝ) / Real.log N ^ (3 : ℕ) := by
    simpa [Q, Real.rpow_natCast] using hBVN hN₂
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hcerrN := hcerr N hN₀ hEven
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hδU : 0 < δ * U := mul_pos hδ hU
  have hBVtiny :
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
        (δ * U / 16) * (N : ℝ) / Real.log N ^ (2 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hcerrN
      (show 0 ≤ δ * U / 4 by positivity)
    calc
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) =
          (δ * U / 4) *
            (cerr * (N : ℝ) / Real.log N ^ (3 : ℕ)) := by
        dsimp [cerr]
        field_simp [hδU.ne']
      _ ≤ (δ * U / 4) *
          ((1 / 4 : ℝ) * (N : ℝ) / Real.log N ^ (2 : ℕ)) := hscaled
      _ = (δ * U / 16) * (N : ℝ) / Real.log N ^ (2 : ℕ) := by ring
  have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℕ) :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  have hUle : U ≤ SingularSeries.liuSingularSeries N := by
    simpa [U] using SingularSeries.liuUniversalProduct_le_liuSingularSeries N
  have hcoeff :
      δ * U / 16 ≤ δ / 2 * SingularSeries.liuSingularSeries N := by
    calc
      δ * U / 16 = (δ / 16) * U := by ring
      _ ≤ (δ / 16) * SingularSeries.liuSingularSeries N :=
        mul_le_mul_of_nonneg_left hUle (by positivity)
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N :=
        mul_le_mul_of_nonneg_right (by linarith) (SingularSeries.liuSingularSeries_pos N).le
  have hBVsmall :
      (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
    calc
      (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
          ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q := hmaxSum
      _ ≤ C * (N : ℝ) / Real.log N ^ (3 : ℕ) := hBVsum
      _ ≤ (δ * U / 16) * (N : ℝ) / Real.log N ^ (2 : ℕ) := hBVtiny
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_right hcoeff hscale
  have hEndpoint :
      (D.card : ℝ) * E.card ≤
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
    calc
      (D.card : ℝ) * E.card ≤
          2 * (N : ℝ) ^ (1 / 2 - ε) * Real.log N / Real.log 2 := by
        simpa [D, E] using
          jurkatRichertSource_exceptional_endpoint_le N ε hN₂ hε hεHalf
      _ ≤ (δ / 2) * U * (N : ℝ) / Real.log N ^ (2 : ℕ) := hendpointN
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
        have hhalfU :
            (δ / 2) * U ≤ (δ / 2) * SingularSeries.liuSingularSeries N :=
          mul_le_mul_of_nonneg_left hUle (by positivity)
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_right hhalfU hscale
  have hreduction :=
    jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional N ε hEven hNgt
  change jurkatRichertSourceRemainderSum N ε ≤ _
  calc
    jurkatRichertSourceRemainderSum N ε ≤
        (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) +
          (D.card : ℝ) * E.card := by
      simpa [D, E] using hreduction
    _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) +
        ((δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ)) :=
      add_le_add hBVsmall hEndpoint
    _ = δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by ring

/-- Chen equation (25), in the one-sided form needed here: the source
Goldbach main term has normalization `20 exp(-γ) 𝔖(N) N / log² N`. -/
def ChenJurkatRichertBaseMertensNormalization : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (jurkatRichertMertensFactor - δ) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log N ^ (2 : ℕ) ≤
        (jurkatRichertSourceBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N)

/-- The literal source cutoff has logarithmic scale `1/10`. -/
theorem tendsto_log_jurkatRichertSourceZ_sub_one_div_log :
    Filter.Tendsto (fun N : ℕ =>
      Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) / Real.log (N : ℝ))
      Filter.atTop (nhds (1 / 10 : ℝ)) := by
  simpa [jurkatRichertSourceZ] using
    (LiuWeight.tendsto_log_floor_rpow_div_log (1 / 10 : ℝ) (by norm_num))

/-- Eventually the source cutoff is one past the corrected cutoff. -/
private theorem eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ :
    ∀ᶠ N : ℕ in Filter.atTop,
      jurkatRichertSourceZ N - 1 = correctedChenZ N := by
  filter_upwards [Filter.eventually_ge_atTop (3 ^ 10)] with N hN
  have hz : 2 ≤ correctedChenZ N - 1 :=
    correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num) (by simpa using hN)
  have hf : 2 ≤ Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) := by
    unfold correctedChenZ at hz
    omega
  unfold jurkatRichertSourceZ correctedChenZ
  rw [max_eq_right hf]
  omega

private theorem tendsto_jurkatRichertSourceZ_sub_one_atTop :
    Filter.Tendsto (fun N : ℕ => jurkatRichertSourceZ N - 1)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      tendsto_correctedChenZ_sub_one_atTop.eventually
        (Filter.eventually_ge_atTop b)] with N heq hN
  rw [heq]
  omega

/-- Adjoining one cutoff point loses at most its universal local factor. -/
private theorem singularSeriesTruncated_one_step_lower (N m : ℕ) (hm : 3 ≤ m) :
    (1 - 1 / ((m : ℝ) - 1) ^ 2) *
        SingularSeries.singularSeriesTruncated N (m - 1) ≤
      SingularSeries.singularSeriesTruncated N m := by
  unfold SingularSeries.singularSeriesTruncated
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  simp only [Finset.prod_filter, Finset.prod_range_succ]
  have hprod : 0 ≤ ∏ x ∈ Finset.range m,
      if x.Prime then SingularSeries.localFactor x N else 1 := by
    apply Finset.prod_nonneg
    intro p hp
    split_ifs with hprime
    · exact (SingularSeries.localFactor_pos hprime).le
    · norm_num
  have hfactor : 1 - 1 / ((m : ℝ) - 1) ^ 2 ≤
      if m.Prime then SingularSeries.localFactor m N else 1 := by
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    by_cases hp : m.Prime
    · simp only [hp, if_true]
      by_cases hpdvd : m ∣ N
      · rw [SingularSeries.localFactor_of_dvd hp (by omega) hpdvd]
        field_simp [hm1.ne']
        nlinarith [show (0 : ℝ) ≤ m by positivity]
      · rw [SingularSeries.localFactor_of_not_dvd hp (by omega) hpdvd]
        field_simp [hm1.ne']
        ring_nf
        rfl
    · simp only [hp, if_false]
      have : 0 ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
      linarith
  calc
    (1 - 1 / ((m : ℝ) - 1) ^ 2) *
          (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) =
        (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) *
          (1 - 1 / ((m : ℝ) - 1) ^ 2) := by ring
    _ ≤ (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) *
          (if m.Prime then SingularSeries.localFactor m N else 1) :=
      mul_le_mul_of_nonneg_left hfactor hprod

private theorem tendsto_source_cutoff_one_step_factor :
    Filter.Tendsto (fun N : ℕ =>
      1 - 1 / ((correctedChenZ N - 1 : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds 1) := by
  have hz : Filter.Tendsto
      (fun N : ℕ => ((correctedChenZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_correctedChenZ_sub_one_atTop
  have hinv : Filter.Tendsto
      (fun N : ℕ => (((correctedChenZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hz
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa [one_div, inv_pow] using hone.sub (hinv.pow 2)

/-- Uniform varying-`N` comparison at Chen's literal source cutoff. -/
theorem eventually_two_mul_liuSingularSeries_le_source_truncated
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      2 * SingularSeries.liuSingularSeries N ≤
        (1 + η) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (jurkatRichertSourceZ N - 1) := by
  have hold :=
    eventually_two_mul_liuSingularSeries_le_truncated (η / 2) (by positivity)
  have hthreshold : (1 + η / 2) / (1 + η) < (1 : ℝ) := by
    rw [div_lt_one (by linarith)]
    linarith
  have hfactor :=
    tendsto_source_cutoff_one_step_factor.eventually
      (Ici_mem_nhds hthreshold)
  filter_upwards [hold, hfactor,
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N holdN hfactorN heq hN
  intro hEven
  let a : ℝ := 1 - 1 / ((correctedChenZ N - 1 : ℕ) : ℝ) ^ 2
  have ha : (1 + η / 2) / (1 + η) ≤ a := by
    simpa [a] using hfactorN
  have ha_pos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hcoef : 1 + η / 2 ≤ a * (1 + η) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + η)] at ha
    nlinarith
  have hm : 3 ≤ correctedChenZ N := by
    have := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    omega
  have hstep := singularSeriesTruncated_one_step_lower N (correctedChenZ N) hm
  have hstep' :
      a * SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) ≤
        SingularSeries.singularSeriesTruncated N (correctedChenZ N) := by
    dsimp [a]
    convert hstep using 1
    rw [Nat.cast_sub (by omega : 1 ≤ correctedChenZ N)]
    norm_num
  have holdN' : 2 * SingularSeries.liuSingularSeries N ≤
      (1 + η / 2) * SingularSeries.singularSeriesTruncated N
        (correctedChenZ N - 1) := by
    simpa only [singularSeriesTruncated_eq_ant] using holdN hEven
  have htruncpos :
      0 < SingularSeries.singularSeriesTruncated N (correctedChenZ N) :=
    SingularSeries.singularSeriesTruncated_pos N _ (by omega)
  apply le_of_mul_le_mul_left _ ha_pos
  calc
    a * (2 * SingularSeries.liuSingularSeries N) ≤
        a * ((1 + η / 2) *
          SingularSeries.singularSeriesTruncated N
            (correctedChenZ N - 1)) :=
      mul_le_mul_of_nonneg_left holdN' ha_pos.le
    _ = (1 + η / 2) *
          (a * SingularSeries.singularSeriesTruncated N
            (correctedChenZ N - 1)) := by ring
    _ ≤ (1 + η / 2) *
          SingularSeries.singularSeriesTruncated N (correctedChenZ N) :=
      mul_le_mul_of_nonneg_left hstep' (by linarith)
    _ ≤ (a * (1 + η)) *
          SingularSeries.singularSeriesTruncated N (correctedChenZ N) :=
      mul_le_mul_of_nonneg_right hcoef htruncpos.le
    _ = a * ((1 + η) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1)) := by
      rw [heq, ← singularSeriesTruncated_eq_ant]
      ring

private theorem tendsto_jurkatRichertMertensCoefficient (C : ℝ) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) *
        (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2))
      Filter.atTop
      (nhds (10 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have hqinv := tendsto_log_jurkatRichertSourceZ_sub_one_div_log.inv₀
    (by norm_num : (1 / 10 : ℝ) ≠ 0)
  have hmR : Filter.Tendsto
      (fun N : ℕ => ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_jurkatRichertSourceZ_sub_one_atTop
  have hlogm : Filter.Tendsto
      (fun N : ℕ => Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hmR
  have hloginv : Filter.Tendsto
      (fun N : ℕ => (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlogm
  have hE : Filter.Tendsto
      (fun _ : ℕ => Real.exp (-Real.eulerMascheroniConstant))
      Filter.atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
    tendsto_const_nhds
  have hC : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have hmain := (hE.mul hqinv).sub ((hC.mul hqinv).mul hloginv)
  have hmain' : Filter.Tendsto (fun N : ℕ =>
      Real.exp (-Real.eulerMascheroniConstant) *
          (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹ -
        (C * (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹) *
          (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop
      (nhds (10 * Real.exp (-Real.eulerMascheroniConstant))) := by
    convert hmain using 1
    norm_num
    ring
  apply hmain'.congr'
  filter_upwards [eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N heq hN
  have hNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
    (show (2 + 1) ^ 10 ≤ N by simpa using hN)
  have hm : 3 ≤ jurkatRichertSourceZ N - 1 := by
    rw [heq]
    omega
  have hmlog :
      0 < Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) :=
    Real.log_pos
      (by exact_mod_cast (by omega : 1 < jurkatRichertSourceZ N - 1))
  field_simp [hNpos.ne', hmlog.ne']

/-- Mertens' product theorem at the literal source cutoff, uniformly in `N`. -/
theorem eventually_jurkatRichertSourceGoldbachSieveProduct_lower
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) / Real.log (N : ℝ) ≤
        MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
  obtain ⟨C, hC⟩ := MertensTheorem.sieve_product_asymptotic
  have hcoef := (tendsto_jurkatRichertMertensCoefficient C).eventually
    (Ici_mem_nhds (by linarith :
      10 * Real.exp (-Real.eulerMascheroniConstant) - ε <
        10 * Real.exp (-Real.eulerMascheroniConstant)))
  filter_upwards [hcoef,
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N hcoefN heq hN
  intro hEven
  have hN4 : 4 ≤ N := by omega
  have hz3 : 3 ≤ jurkatRichertSourceZ N := by
    have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    have hc3 : 3 ≤ correctedChenZ N := by omega
    have hs3 : 3 ≤ jurkatRichertSourceZ N - 1 := by
      rw [heq]
      exact hc3
    omega
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have htruncpos : 0 < SingularSeries.singularSeriesTruncated N
      (jurkatRichertSourceZ N - 1) :=
    SingularSeries.singularSeriesTruncated_pos N _ (by omega)
  have hasym := hC N (jurkatRichertSourceZ N) hz3 hEven hN4
  have hlower := (abs_le.mp hasym).1
  have hproduct :
      SingularSeries.singularSeriesTruncated N (jurkatRichertSourceZ N - 1) *
          Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
        C * SingularSeries.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) /
          Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 ≤
        MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    linarith
  have hcoeffdiv :
      (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) /
          Real.log (N : ℝ) ≤
        Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 := by
    rw [div_le_iff₀ hlogN]
    nlinarith
  calc
    (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) / Real.log (N : ℝ) =
        ((10 * Real.exp (-Real.eulerMascheroniConstant) - ε) /
          Real.log (N : ℝ)) *
          SingularSeries.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) := by
      rw [singularSeriesTruncated_eq_ant]
      ring
    _ ≤ (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) *
          SingularSeries.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) :=
      mul_le_mul_of_nonneg_right hcoeffdiv htruncpos.le
    _ ≤ MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
      convert hproduct using 1
      ring

/-- Chen's equation (25) follows from the exact Goldbach product identity,
Mertens' product theorem, and the uniform source-cutoff singular-series bridge. -/
theorem chenJurkatRichertBaseMertensNormalization :
    ChenJurkatRichertBaseMertensNormalization := by
  intro δ hδ
  let B := jurkatRichertMertensFactor
  have hB : 0 < B := by
    simpa [B] using jurkatRichertMertensFactor_pos
  let δ' := min δ (B / 2)
  have hδ' : 0 < δ' := lt_min hδ (half_pos hB)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'B : δ' ≤ B / 2 := min_le_right _ _
  let η := δ' / (2 * B)
  let ε := δ' / 8
  have hη : 0 < η := div_pos hδ' (by positivity)
  have hε : 0 < ε := by positivity
  have hseries :=
    eventually_two_mul_liuSingularSeries_le_source_truncated η hη
  have hmertens :=
    eventually_jurkatRichertSourceGoldbachSieveProduct_lower ε hε
  filter_upwards [hseries, hmertens,
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N hseriesN hmertensN heq hN
  intro hEven
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let S := SingularSeries.liuSingularSeries N
  let T := AnalyticNumberTheory.Sieve.singularSeriesTruncated N
    (jurkatRichertSourceZ N - 1)
  have hS : 0 < S := by
    simpa [S] using SingularSeries.liuSingularSeries_pos N
  have hT : 0 < T := by
    dsimp [T]
    rw [← singularSeriesTruncated_eq_ant]
    apply SingularSeries.singularSeriesTruncated_pos N _
    have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    rw [heq]
    omega
  have hseriesN' : 2 * S ≤ (1 + η) * T := by
    simpa [S, T] using hseriesN hEven
  have hBdef : B = 20 * Real.exp (-Real.eulerMascheroniConstant) := by
    rfl
  have hBminus : 0 ≤ B - δ' := by nlinarith
  have hcoef :
      (B - δ') * (1 + η) / 2 ≤
        10 * Real.exp (-Real.eulerMascheroniConstant) - ε := by
    dsimp [η, ε]
    rw [hBdef]
    field_simp [hB.ne']
    nlinarith [sq_nonneg δ']
  have hseriesScaled :
      (B - δ) * S ≤
        (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T := by
    calc
      (B - δ) * S ≤ (B - δ') * S :=
        mul_le_mul_of_nonneg_right (by linarith) hS.le
      _ = ((B - δ') / 2) * (2 * S) := by ring
      _ ≤ ((B - δ') / 2) * ((1 + η) * T) :=
        mul_le_mul_of_nonneg_left hseriesN'
          (div_nonneg hBminus (by norm_num))
      _ = ((B - δ') * (1 + η) / 2) * T := by ring
      _ ≤ (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T :=
        mul_le_mul_of_nonneg_right hcoef hT.le
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  have hleft :
      (B - δ) * S * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) ≤
        (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_right hseriesScaled hscale)
  have hmertensN' :
      (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T /
          Real.log (N : ℝ) ≤
        MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    simpa [T] using hmertensN hEven
  have hmass : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlogN.le
  have hright := mul_le_mul_of_nonneg_left hmertensN' hmass
  have hproduct : 0 ≤ MertensTheorem.goldbachSieveProduct N
      (jurkatRichertSourceZ N) := by
    rw [← jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p
        (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero
          (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le
  have hmassLower :
      (N : ℝ) / Real.log (N : ℝ) ≤
        LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N := by
    apply LiuWeight.div_log_le_liuLogarithmicIntegral
    exact_mod_cast (show 2 ≤ N by omega)
  calc
    (jurkatRichertMertensFactor - δ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) =
        (B - δ) * S * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
      rfl
    _ ≤ (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := hleft
    _ = ((N : ℝ) / Real.log (N : ℝ)) *
          ((10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T /
            Real.log (N : ℝ)) := by ring
    _ ≤ ((N : ℝ) / Real.log (N : ℝ)) *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) :=
      hright
    _ ≤ LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) :=
      mul_le_mul_of_nonneg_right hmassLower hproduct
    _ = (jurkatRichertSourceBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
           (jurkatRichertSourceBoundingSieve N) := by
      rw [jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
      rfl

private theorem tendsto_jurkatRichertMertensUpperCoefficient (C : ℝ) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) *
        (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2))
      Filter.atTop
      (nhds (10 * Real.exp (-Real.eulerMascheroniConstant))) := by
  simpa only [neg_div, sub_neg_eq_add] using
    tendsto_jurkatRichertMertensCoefficient (-C)

/-- Mertens' product theorem at the literal source cutoff, with Liu's genuine
normalization and an upper error uniform in the even integer `N`. -/
theorem eventually_jurkatRichertSourceGoldbachSieveProduct_upper
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
        (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ) := by
  let B := 10 * Real.exp (-Real.eulerMascheroniConstant)
  have hB : 0 < B := by positivity
  let d := min 1 (η / (4 * (B + 2)))
  have hd : 0 < d := lt_min (by norm_num)
    (div_pos hη (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdη : d * (B + 2) ≤ η / 4 := by
    have := min_le_right (1 : ℝ) (η / (4 * (B + 2)))
    dsimp [d] at *
    apply (le_div_iff₀ (by positivity : 0 < 4 * (B + 2))).mp at this
    nlinarith
  obtain ⟨C, hC⟩ := MertensTheorem.sieve_product_asymptotic
  have hcoef := (tendsto_jurkatRichertMertensUpperCoefficient C).eventually
    (Iic_mem_nhds (by linarith :
      B < B + d))
  have hseriesRaw :=
    SingularSeries.eventually_liuSingularSeriesTruncated_le d hd
  have hzAtTop := tendsto_jurkatRichertSourceZ_sub_one_atTop.eventually hseriesRaw
  filter_upwards [hcoef, hzAtTop,
      Filter.eventually_ge_atTop (3 ^ 10),
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ] with
      N hcoefN hseriesN hN heq
  intro hEven
  have hN4 : 4 ≤ N := by omega
  have hz3 : 3 ≤ jurkatRichertSourceZ N := by
    have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    have : 3 ≤ correctedChenZ N := by omega
    rw [← heq] at this
    omega
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hz2 : 2 ≤ jurkatRichertSourceZ N - 1 := by omega
  let T := SingularSeries.singularSeriesTruncated N
    (jurkatRichertSourceZ N - 1)
  let S := SingularSeries.liuSingularSeries N
  have hT : 0 < T := by
    dsimp [T]
    exact SingularSeries.singularSeriesTruncated_pos N _ (by omega)
  have hS : 0 < S := by
    simpa [S] using SingularSeries.liuSingularSeries_pos N
  have hasym := hC N (jurkatRichertSourceZ N) hz3 hEven hN4
  have hproduct :
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
        T * (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) := by
    calc
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
          T * Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
            C * T / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 := by
        dsimp [T]
        linarith [(abs_le.mp hasym).2]
      _ = T * (Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
            C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) := by ring
  have hcoefficient :
      Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 ≤
        (B + d) / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlogN).2
    simpa [B, mul_comm] using hcoefN
  have hlegacy : T ≤ 2 * (1 + d) * S := by
    rw [show T = 2 * SingularSeries.liuSingularSeriesTruncated N
        (jurkatRichertSourceZ N - 1) by
      dsimp [T]
      exact SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
        N _ hEven hz2]
    simpa [S, mul_assoc] using
      mul_le_mul_of_nonneg_left (hseriesN N (by omega)) (by norm_num : (0 : ℝ) ≤ 2)
  have hfinalCoefficient : 2 * (B + d) * (1 + d) ≤ 2 * B + η := by
    have hdsq : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
    nlinarith
  calc
    MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
        T * (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) := hproduct
    _ ≤ T * ((B + d) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoefficient hT.le
    _ ≤ (2 * (1 + d) * S) * ((B + d) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hlegacy
        (div_nonneg (by linarith) hlogN.le)
    _ = (2 * (B + d) * (1 + d)) * S / Real.log (N : ℝ) := by ring
    _ ≤ (2 * B + η) * S / Real.log (N : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfinalCoefficient hS.le) hlogN.le
    _ = (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ) := by
      dsimp [B, S]
      ring

/-- The genuine logarithmic integral has the sharp upper normalization needed
when it is multiplied by the Mertens sieve product. -/
theorem eventually_liuLogarithmicIntegral_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N ≤
        (1 + η) * (N : ℝ) / Real.log (N : ℝ) := by
  obtain ⟨C, hC, hrem⟩ :=
    LiuWeight.eventually_abs_liuLogarithmicIntegralRemainder_le
      (2 / Real.log 2)
  have hlogAtTop : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlogAtTop.eventually
    (Filter.eventually_ge_atTop (C / η))
  have hremNat := tendsto_natCast_atTop_atTop.eventually hrem
  filter_upwards [hremNat, hlarge, Filter.eventually_ge_atTop 2] with N hremN hlargeN hN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hCoverLog : C / Real.log (N : ℝ) ≤ η := by
    rw [div_le_iff₀ hlogN]
    have := (div_le_iff₀ hη).mp hlargeN
    nlinarith
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) := by positivity
  have herror :
      C * (N : ℝ) / Real.log (N : ℝ) ^ 2 ≤
        η * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      C * (N : ℝ) / Real.log (N : ℝ) ^ 2 =
          (C / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
      _ ≤ η * ((N : ℝ) / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hCoverLog hscale
  have hremainder :
      LiuWeight.liuLogarithmicIntegralRemainder (2 / Real.log 2) N ≤
        η * ((N : ℝ) / Real.log (N : ℝ)) :=
    (le_abs_self _).trans ((hremN (by exact_mod_cast hN)).trans herror)
  unfold LiuWeight.liuLogarithmicIntegralRemainder at hremainder
  calc
    LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N =
        (N : ℝ) / Real.log (N : ℝ) +
          (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N -
            (N : ℝ) / Real.log (N : ℝ)) := by ring
    _ ≤ (N : ℝ) / Real.log (N : ℝ) +
        η * ((N : ℝ) / Real.log (N : ℝ)) :=
      by simpa [add_comm] using
        add_le_add_left hremainder ((N : ℝ) / Real.log (N : ℝ))
    _ = (1 + η) * (N : ℝ) / Real.log (N : ℝ) := by ring

/-- The common mass in every conditioned source sieve has the sharp
Liu-normalized upper asymptotic. -/
theorem eventually_jurkatRichertSourceCommonDensity_upper
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) ≤
        (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℕ) := by
  let B := 20 * Real.exp (-Real.eulerMascheroniConstant)
  have hB : 0 < B := by positivity
  let d := min 1 (η / (B + 2))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hη (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdη : d * (B + 2) ≤ η := by
    have := min_le_right (1 : ℝ) (η / (B + 2))
    dsimp [d] at *
    exact (le_div_iff₀ (by positivity : 0 < B + 2)).mp this
  have hcoef : (1 + d) * (B + d) ≤ B + η := by
    have hdsq : d ^ 2 ≤ d := by
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
    nlinarith
  have hli := eventually_liuLogarithmicIntegral_le d hd
  have hproduct := eventually_jurkatRichertSourceGoldbachSieveProduct_upper d hd
  filter_upwards [hli, hproduct, Filter.eventually_ge_atTop 2] with
      N hliN hproductN hN
  intro hEven
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hgoldbachNonneg :
      0 ≤ MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    rw [← jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p
        (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero
          (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le
  have hscale : 0 ≤ (1 + d) * (N : ℝ) / Real.log (N : ℝ) := by positivity
  have hS : 0 ≤ SingularSeries.liuSingularSeries N :=
    (SingularSeries.liuSingularSeries_pos N).le
  calc
    LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) =
        LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
      rw [jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    _ ≤ ((1 + d) * (N : ℝ) / Real.log (N : ℝ)) *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) :=
      mul_le_mul_of_nonneg_right hliN hgoldbachNonneg
    _ ≤ ((1 + d) * (N : ℝ) / Real.log (N : ℝ)) *
          ((B + d) * SingularSeries.liuSingularSeries N /
            Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa [B] using hproductN hEven) hscale
    _ = ((1 + d) * (B + d)) * SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by ring
    _ ≤ (B + η) * SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
      have hright : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℕ) := by positivity
      simpa [mul_assoc, mul_div_assoc] using
        mul_le_mul_of_nonneg_right hcoef hright
    _ = (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℕ) := by rfl

/-- The base term in Chen's equation (26), using equation (25) for its
Mertens normalization. -/
def ChenJurkatRichertBaseLowerSieveAsymptotic : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (jurkatRichertBaseMainCoefficient jurkatRichertJ - η) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log N ^ (2 : ℕ) ≤
        ((jurkatRichertSourceCandidates N).card : ℝ)

/-- The literal base asymptotic follows from the level-`N^(1/2-ε)` lower-sieve
fundamental lemma and Goldbach AP distribution for its finite remainder.
Equation (25)'s Mertens normalization is unconditional. -/
theorem chenJurkatRichertBaseLowerSieveAsymptotic_of_inputs
    (hlower : ChenJurkatRichertBaseLowerSieveFundamentalLemma)
    (hdistribution : ChenJurkatRichertBaseGoldbachDistribution) :
    ChenJurkatRichertBaseLowerSieveAsymptotic := by
  intro η hη
  let A := jurkatRichertBaseSieveFactor jurkatRichertJ
  let B := jurkatRichertMertensFactor
  let C := jurkatRichertBaseMainCoefficient jurkatRichertJ
  have hA : 0 < A := by
    simpa [A] using jurkatRichertBaseSieveFactor_pos
  have hB : 0 < B := by
    simpa [B] using jurkatRichertMertensFactor_pos
  have hAB : A * B = C := by
    simpa [A, B, C] using jurkatRichert_sieveFactor_mul_mertensFactor
  have hC : 0 < C := by rw [← hAB]; positivity
  let η' := min η (C / 2)
  have hη' : 0 < η' := lt_min hη (half_pos hC)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'C : η' ≤ C / 2 := min_le_right _ _
  let δA := η' / (8 * B)
  let δB := η' / (8 * A)
  let δR := η' / 2
  have hδA : 0 < δA := div_pos hη' (by positivity)
  have hδB : 0 < δB := div_pos hη' (by positivity)
  have hδR : 0 < δR := half_pos hη'
  have hδAB : δA * B = η' / 8 := by
    dsimp [δA]
    field_simp [hB.ne']
  have hAδB : A * δB = η' / 8 := by
    dsimp [δB]
    field_simp [hA.ne']
  have hδAle : δA ≤ A / 16 := by
    by_contra hnot
    have hlt : A / 16 < δA := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_right hlt hB
    have hleft : A / 16 * B = C / 16 := by rw [← hAB]; ring
    rw [hleft, hδAB] at hmul
    nlinarith
  have hδBle : δB ≤ B / 16 := by
    by_contra hnot
    have hlt : B / 16 < δB := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_right hlt hA
    have hleft : B / 16 * A = C / 16 := by rw [← hAB]; ring
    rw [hleft, mul_comm δB A, hAδB] at hmul
    nlinarith
  have hAminus : 0 ≤ A - δA := by nlinarith
  have hBminus : 0 ≤ B - δB := by nlinarith
  rcases hlower δA hδA with ⟨ε, hε, hεHalf, hLower⟩
  have hDistribution :=
    hdistribution ε hε hεHalf δR hδR
  have hMertens := chenJurkatRichertBaseMertensNormalization δB hδB
  filter_upwards [hLower, hDistribution, hMertens,
      Filter.eventually_ge_atTop 3] with N hLowerN hDistributionN hMertensN hN
  intro hEven
  have hLowerN' := hLowerN hEven
  have hDistributionN' := hDistributionN hEven
  have hMertensN' := hMertensN hEven
  let M : ℝ :=
    SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N))
      (sq_nonneg (Real.log N))
  have hMain :
      (B - δB) * M ≤
        (jurkatRichertSourceBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) := by
    convert hMertensN' using 1
    dsimp [B, M]
    ring
  have hScaled := mul_le_mul_of_nonneg_left hMain hAminus
  have hRemainder :
      jurkatRichertSourceRemainderSum N ε ≤ δR * M := by
    convert hDistributionN' using 1
    dsimp [δR, M]
    ring
  have hFinite :
      (A - δA) * ((B - δB) * M) - δR * M ≤
        (jurkatRichertSourceBoundingSieve N).siftedSum := by
    have hLowerRewritten :
        (A - δA) *
              ((jurkatRichertSourceBoundingSieve N).totalMass *
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                  (jurkatRichertSourceBoundingSieve N)) -
            jurkatRichertSourceRemainderSum N ε ≤
          (jurkatRichertSourceBoundingSieve N).siftedSum := by
      simpa [A] using hLowerN'
    linarith
  have hδProduct : 0 ≤ δA * δB := mul_nonneg hδA.le hδB.le
  have hCoefficient :
      C - η ≤ (A - δA) * (B - δB) - δR := by
    dsimp [δR]
    rw [← hAB]
    nlinarith
  have hTargetScale :
      (C - η) * M ≤ ((A - δA) * (B - δB) - δR) * M :=
    mul_le_mul_of_nonneg_right hCoefficient hM
  have hTarget :
      (C - η) * M ≤
        (jurkatRichertSourceBoundingSieve N).siftedSum := by
    calc
      (C - η) * M ≤ ((A - δA) * (B - δB) - δR) * M :=
        hTargetScale
      _ = (A - δA) * ((B - δB) * M) - δR * M := by ring
      _ ≤ (jurkatRichertSourceBoundingSieve N).siftedSum := hFinite
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hTarget
  convert hTarget using 1
  dsimp [C, M]
  ring


end MathlibNt.SieveTheory.SwitchingPrinciple
