import MathlibNt.Wu2008DoubleSieve.CanonicalUpperDensity
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147JurkatRichertInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDensityBoundingSieveBridge

/-!
# Canonical lower density on the first nonzero interval

Suzuki's all-depth lower theorem is a proved, uniform-in-sieve estimate.
We absorb its even-depth error uniformly on `[2,4]`, retain the actual
coordinate `s = log level / log z`, and identify its factor with the
constructed Jurkat--Richert delay function. No lower fundamental-lemma
proposition is assumed.

Every product and `sourceSieveCount` here uses the strict convention `p < z`.
The printed Wu08 closed convention `p ≤ z` is a different carrier. A lower
bound for the strict count does not imply one for the closed count without
paying their endpoint difference.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Topology
open scoped Classical BigOperators Interval
open AnalyticNumberTheory.Sieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The source-series lower factor is the actual JR delay solution on `[2,4]`.
The normalization uses the proved Suzuki adjoint pairing, not a chosen constant. -/
theorem suzukiContinuousLowerFactor_eq_jr1965f_firstInterval
    {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    suzukiContinuousLowerFactor s = jr1965f s := by
  have hrec := jr1965f_integral_recurrence (v := 2) le_rfl hs2
  have hint :
      (∫ t in (2 : ℝ)..s, jr1965F (t - 1)) =
        (2 * Real.exp Real.eulerMascheroniConstant) *
          ∫ t in (2 : ℝ)..s, (t - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hs2] at ht
    change jr1965F (t - 1) =
      2 * Real.exp Real.eulerMascheroniConstant * (t - 1)⁻¹
    rw [jr1965F_eq_of_le_three (by linarith [ht.2])]
    exact div_eq_mul_inv _ _
  rw [jr1965f_initial le_rfl, mul_zero, zero_add, hint] at hrec
  change 1 - suzukiProposition118SourceTMinus s = _
  rw [one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
    jr1965Section13HatSourceContract hs2 hs4]
  unfold suzukiLowerSieveFactorFirstInterval
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract]
  have hsne : s ≠ 0 := by linarith
  have hf : jr1965f s = (2 * Real.exp Real.eulerMascheroniConstant *
      ∫ t in (2 : ℝ)..s, (t - 1)⁻¹) / s :=
    (eq_div_iff hsne).2 (by simpa only [mul_comm] using hrec)
  rw [hf]
  ring

/-- Wu's first nonzero lower branch, for the constructed global `f`. -/
theorem jr1965f_eq_log_firstInterval {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    jr1965f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  rw [← suzukiContinuousLowerFactor_eq_jr1965f_firstInterval hs2 hs4]
  change 1 - suzukiProposition118SourceTMinus s = _
  rw [one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
    jr1965Section13HatSourceContract hs2 hs4,
    suzukiLowerSieveFactorFirstInterval_eq_log hs2 hs4,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]

theorem jr1965f_pos_firstInterval {s : ℝ} (hs2 : 2 < s) (hs4 : s ≤ 4) :
    0 < jr1965f s := by
  rw [jr1965f_eq_log_firstInterval hs2.le hs4]
  exact div_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (Real.log_pos (by linarith))) (by linarith)

/-- The actual coefficient `a(s)` in Wu08 (3.3), on this proved branch. -/
theorem jr1965f_normalized_firstInterval {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    s * jr1965f s / (2 * Real.exp Real.eulerMascheroniConstant) = Real.log (s - 1) := by
  rw [jr1965f_eq_log_firstInterval hs2 hs4]
  have hsne : s ≠ 0 := by linarith
  have he : Real.exp Real.eulerMascheroniConstant ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- The literal even-depth error is bounded on the first lower window.
Its depth can depend on the entire growing prime carrier. -/
theorem lower_errorEnvelope_even_le_sixteen
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {n : ℕ} (hn : Even n) {D d s : ℝ}
    (hd : 0 ≤ d) (hD : 1 < D) (hlog : 4 ^ d ≤ Real.log D)
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    errorEnvelope H n D d s ≤ 16 := by
  have hs0 : 0 ≤ s := by linarith
  have hsd : s ^ d ≤ (4 : ℝ) ^ d :=
    Real.rpow_le_rpow hs0 hs4 hd
  have hlogpos : 0 < Real.log D := Real.log_pos hD
  have hratio : s ^ d / Real.log D ≤ 1 :=
    (div_le_one hlogpos).2 (hsd.trans hlog)
  have hbase0 : 0 ≤ 1 + s ^ d / Real.log D := by positivity
  have hperturb : (1 + s ^ d / Real.log D) ^ s ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) ^ s := Real.rpow_le_rpow hbase0 (by linarith) hs0
      _ ≤ (2 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hs4
      _ = 16 := by norm_num
  have hanti : AntitoneOn (weightedHat H .minus) (Icc (2 : ℝ) s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (2 : ℝ) s)
    · exact (continuousOn_id.pow 2).mul (hH.continuous .minus) |>.mono (by
        intro x hx
        change 0 < x
        linarith [hx.1])
    · intro x hx
      have hx' : x ∈ Ioo (2 : ℝ) s := by simpa only [interior_Icc] using hx
      exact (hH.dde .minus x (by
        simp [ErrorSign.epsilon]
        linarith [hx'.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (2 : ℝ) s := by simpa only [interior_Icc] using hx
      rw [(hH.dde .minus x (by
        simp [ErrorSign.epsilon]
        linarith [hx'.1])).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx'.1])
        (hH.positive .plus (x - 1) (by linarith [hx'.1])).le
  have hweighted := hanti ⟨le_rfl, hs2⟩ ⟨hs2, le_rfl⟩ hs2
  rw [hH.initial_minus 2 (by norm_num) le_rfl] at hweighted
  have hT : 0 ≤ H.Tminus s := (hH.positive .minus s (by linarith)).le
  have hsT : s * H.Tminus s ≤ 1 := by
    have hw : s ^ 2 * H.Tminus s ≤ 2 := by
      simpa [weightedHat, Section13HatLayers.T] using hweighted
    have hmul := mul_le_mul_of_nonneg_right hs2 (mul_nonneg hs0 hT)
    nlinarith
  rw [errorEnvelope_even hn]
  calc
    _ = (1 + s ^ d / Real.log D) ^ s * (s * H.Tminus s) := by ring
    _ ≤ 16 * 1 :=
      mul_le_mul hperturb hsT (mul_nonneg hs0 hT) (by norm_num)
    _ = 16 := by norm_num

/-- Uniform scalar absorption, simultaneously for every even depth and every
source coordinate in `[2,4]`. -/
theorem eventually_lower_even_depth_error_small
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {C K d δ ρ : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d) (hδ : 0 < δ)
    (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ n : ℕ, Even n → ∀ s : ℝ,
      2 ≤ s → s ≤ 4 →
      C * Real.exp (Real.sqrt K) * errorEnvelope H n D d s *
        (Real.log D) ^ (-δ) < ρ := by
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop
  let A : ℝ := C * Real.exp (Real.sqrt K) * 16
  have hsmall : ∀ᶠ D : ℝ in atTop, A * (Real.log D) ^ (-δ) < ρ := by
    have hmul : Tendsto (fun D : ℝ => A * (Real.log D) ^ (-δ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hdecay.const_mul A
    exact (tendsto_order.1 hmul).2 ρ hρ
  have hlargeLog : ∀ᶠ D : ℝ in atTop, (4 : ℝ) ^ d ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((4 : ℝ) ^ d))
  filter_upwards [hsmall, hlargeLog, eventually_gt_atTop (1 : ℝ)] with
    D hsmallD hlogD hD
  intro n hn s hs2 hs4
  have hE := lower_errorEnvelope_even_le_sixteen H hH hn hd hD hlogD hs2 hs4
  have hdecay0 : 0 ≤ (Real.log D) ^ (-δ) :=
    Real.rpow_nonneg (Real.log_pos hD).le _
  calc
    _ ≤ A * (Real.log D) ^ (-δ) := by
      apply mul_le_mul_of_nonneg_right _ hdecay0
      exact mul_le_mul_of_nonneg_left hE (mul_nonneg hC (Real.exp_pos _).le)
    _ < ρ := hsmallD

/-- A proved canonical lower fundamental lemma on `[2,4]`. The threshold is
chosen before the finite sieve, cutoff, level and ratio. -/
theorem canonical_lower_density_fundamentalLemma
    {K ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ (S : BoundingSieve) (z level s : ℝ),
      z0 ≤ z → 2 ≤ z → 0 < level →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log level / Real.log z → 2 ≤ s → s ≤ 4 →
      (jr1965f s - ρ) * sieveProductPrimeFactors S ≤
        S.mainSum (lowerRosserWeight S.prodPrimes (⌊level⌋₊ + 1)) := by
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, _, hall⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_C145, _Clow, C, _, _, hC, hnat⟩ := hall C1min le_rfl
  let K' : ℝ := max 2 K
  have hK' : 2 ≤ K' := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨Dσ, _, hDσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) 4 (by norm_num)
  obtain ⟨DE, hDE⟩ := eventually_atTop.1
    (eventually_lower_even_depth_error_small jr1965Section13HatLayers
      jr1965Section13HatSourceContract.toSection13HatContract
      (C := C) (K := K') (d := 16) (δ := 1 / 2) hC0
      (by norm_num) (by norm_num) hρ)
  refine ⟨max 2 (max Dσ DE), ?_⟩
  intro S z level s hz0 hz2 hlevel hlocal hcut hs hs2 hs4
  let D : ℕ := ⌊level⌋₊ + 1
  let Z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let n : ℕ := 2 * ((suzukiSupportedBelow S Z).card + 1)
  have hgeom := real_level_to_natCeil_geometry hz2 hlevel hs (by linarith)
  have hD2 : 2 ≤ D := hgeom.1
  have hroot : z < (D : ℝ) ^ (1 / s) := hgeom.2.2.1
  have hZ2 : 2 ≤ Z := hgeom.2.2.2
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hloglevel : Real.log z ≤ Real.log level := by
    have hratio : 1 ≤ Real.log level / Real.log z := by rw [← hs]; linarith
    simpa only [one_mul] using (le_div_iff₀ hlogz).mp hratio
  have hzlevel : z ≤ level := (Real.log_le_log_iff (by linarith) hlevel).mp hloglevel
  have hzD : z < (D : ℝ) := hzlevel.trans_lt hgeom.2.1
  have hzσ : Dσ ≤ z :=
    (le_max_left Dσ DE).trans ((le_max_right 2 (max Dσ DE)).trans hz0)
  have hzE : DE ≤ z :=
    (le_max_right Dσ DE).trans ((le_max_right 2 (max Dσ DE)).trans hz0)
  have hsσ : s ≤ sourceSigma (D : ℝ) 16 :=
    hs4.trans (hDσ _ (hzσ.trans hzD.le))
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono hlocal (le_max_right _ _)
  have hcutZ : ∀ p ∈ S.prodPrimes.primeFactors, p < Z := by
    intro p hp
    exact Nat.lt_ceil.mpr ((hcut p hp).trans_lt hroot)
  have hcutD : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact_mod_cast (hcut p hp).trans_lt hzD
  have hmain := hnat S K' hK' hlocal' D hD2 s hs2 hsσ hZ2
  change suzukiVProduct S (Z : ℝ) *
      (suzukiContinuousLowerFactor s -
        C * Real.exp (Real.sqrt K') * errorEnvelope jr1965Section13HatLayers n
          (D : ℝ) 16 s * (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S Z) at hmain
  have herr := hDE (D : ℝ) (hzE.trans hzD.le) n (even_two_mul _) s hs2 hs4
  have hV : 0 ≤ suzukiVProduct S (Z : ℝ) := (suzukiVProduct_pos S _).le
  have hbound : suzukiVProduct S (Z : ℝ) * (jr1965f s - ρ) ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S Z) := by
    rw [suzukiContinuousLowerFactor_eq_jr1965f_firstInterval hs2 hs4] at hmain
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left herr.le _) hV).trans hmain
  have hbridge := suzukiDensityProduct_lowerRosserWeight_exact_bridge S D Z hcutZ hcutD
  rw [hbridge.2.1, ← hbridge.1] at hbound
  simpa only [mul_comm] using hbound

/-- Exact lower-weight version of the ordinary Goldbach main-sum bridge. -/
theorem ordinaryGoldbach_lower_mainSum_eq (N d D : ℕ) (he : Even N) (z : ℝ) :
    (ordinaryGoldbachBoundingSieve N d he z).mainSum
      (lowerRosserWeight (ordinaryGoldbachBoundingSieve N d he z).prodPrimes D) =
        ordinaryRosserMainSum false N d D z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  change (∑ q ∈ (ordinarySievePrimeProduct (d * N) z).divisors,
      lowerRosserWeight _ D q * goldbachNu q) = _
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree _ _).squarefree_of_dvd
      (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, Bool.false_eq_true, if_false, div_eq_mul_inv, one_mul]
  rfl

/-- Actual uniform Goldbach density with the canonical nonzero lower branch.
The Euler product belongs to the selected modulus `d*N`. -/
theorem ordinaryRosser_lower_density_canonical {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 2 ≤ s → s ≤ 4 →
      (jr1965f s - ρ) *
          ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1)) ≤
        ordinaryRosserMainSum false N d (⌊level⌋₊ + 1) z := by
  obtain ⟨K, _, hdim⟩ := ordinaryGoldbach_uniform_dimension_one
  obtain ⟨z0, hbound⟩ := canonical_lower_density_fundamentalLemma (K := K) hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hs2 hs4
  have hcut : ∀ p ∈ (ordinaryGoldbachBoundingSieve N d he z).prodPrimes.primeFactors,
      (p : ℝ) ≤ z := by
    change ∀ p ∈ (ordinarySievePrimeProduct (d * N) z).primeFactors, (p : ℝ) ≤ z
    rw [ordinarySievePrimeProduct_primeFactors]
    exact fun _p hp => (mem_primeWindow.mp hp).2.2.2.le
  have h := hbound (ordinaryGoldbachBoundingSieve N d he z) z level s hz0 hz hlevel
    (hdim N d he z) hcut hs hs2 hs4
  rw [ordinaryGoldbach_lower_mainSum_eq, ordinaryGoldbach_sieveProduct_eq] at h
  exact h

/-- The lower density in precisely the actual local-product normalization. -/
theorem ordinaryRosser_lower_density_canonical_local {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 2 ≤ s → s ≤ 4 →
      (jr1965f s - ρ) * localSieveProduct (d * N) z ≤
        ordinaryRosserMainSum false N d (⌊level⌋₊ + 1) z := by
  obtain ⟨z0, hbound⟩ := ordinaryRosser_lower_density_canonical hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hs2 hs4
  simpa only [localSieveProduct, localSievePrimes_eq_primeWindow] using
    hbound N d he z level s hz0 hz hlevel hs hs2 hs4

/-- Lower sieve for the actual strict (`p < z`) source with its exact signed
ordinary-AP remainder. This does not bound `sourceSieveCountLE` from below. -/
theorem ordinarySieve_lower_canonical_with_signed_error {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, 2 ≤ N → ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 2 ≤ s → s ≤ 4 →
      (AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N /
        (Nat.totient d : ℝ)) *
          ((jr1965f s - ρ) *
            ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1))) +
          ordinaryRosserRemainder false N d (⌊level⌋₊ + 1) z ≤
        (sourceSieveCount N d (d * N) z : ℝ) := by
  obtain ⟨z0, hdensity⟩ := ordinaryRosser_lower_density_canonical hρ
  refine ⟨z0, ?_⟩
  intro N d he hN z level s hz0 hz hlevel hs hs2 hs4
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hloglevel : Real.log z ≤ Real.log level := by
    have hratio : 1 ≤ Real.log level / Real.log z := by rw [← hs]; linarith
    simpa only [one_mul] using (le_div_iff₀ hlogz).mp hratio
  have hzlevel : z ≤ level := (Real.log_le_log_iff (by linarith) hlevel).mp hloglevel
  have hlevelD : level < (⌊level⌋₊ + 1 : ℕ) := by
    exact_mod_cast Nat.lt_floor_add_one level
  have hfinite := ordinaryRosser_lower_finite (N := N) (d := d)
    (hzlevel.trans hlevelD.le)
  have hden := hdensity N d he z level s hz0 hz hlevel hs hs2 hs4
  have hX : 0 ≤
      AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N /
        (Nat.totient d : ℝ) :=
    div_nonneg (LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN)) (Nat.cast_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hden hX
  linarith

/-- Canonical lower sieve for the strict (`p < z`) count, with the already
proved ordinary-AP budget. The closed-cutoff endpoint difference is not included. -/
theorem ordinarySieve_lower_canonical_with_AP_error {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d Q : ℕ, ∀ _he : Even N, 2 ≤ N → ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 2 ≤ s → s ≤ 4 →
      ⌊level⌋₊ + 1 ≤ Q / d + 1 →
      (AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N /
        (Nat.totient d : ℝ)) *
          ((jr1965f s - ρ) *
            ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1))) -
          ∑ q ∈ (Finset.Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
            |primeAPError N (d * q) N| ≤
        (sourceSieveCount N d (d * N) z : ℝ) := by
  obtain ⟨z0, hbound⟩ := ordinarySieve_lower_canonical_with_signed_error hρ
  refine ⟨z0, ?_⟩
  intro N d Q he hN z level s hz0 hz hlevel hs hs2 hs4 hD
  have h := hbound N d he hN z level s hz0 hz hlevel hs hs2 hs4
  have herr := ordinaryRosserRemainder_le_AP (upper := false) (N := N) (d := d)
    (Q := Q) z hD
  have hneg := neg_abs_le (ordinaryRosserRemainder false N d (⌊level⌋₊ + 1) z)
  linarith

end Wu2008DoubleSieve
