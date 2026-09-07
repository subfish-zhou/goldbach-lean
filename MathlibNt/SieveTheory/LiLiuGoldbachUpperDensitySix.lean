import MathlibNt.SieveTheory.SuzukiUpperRosserDensityEndpointDirect
import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource

open Set Filter Topology
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

noncomputable section

private theorem UpperDensitySix_errorEnvelope_odd_le_sixtyFour
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {N : ℕ} (hN : Odd N) {D d s : ℝ}
    (hd : 0 ≤ d) (hD : 1 < D) (hlog : 6 ^ d ≤ Real.log D)
    (hslo : 3 / 2 ≤ s) (hshi : s ≤ 6) :
    errorEnvelope H N D d s ≤ 64 := by
  have hs0 : 0 ≤ s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hsd : s ^ d ≤ (6 : ℝ) ^ d :=
    Real.rpow_le_rpow hs0 hshi hd
  have hlogpos : 0 < Real.log D := Real.log_pos hD
  have hratio : s ^ d / Real.log D ≤ 1 :=
    (div_le_one hlogpos).2 (hsd.trans hlog)
  have hbase0 : 0 ≤ 1 + s ^ d / Real.log D := by positivity
  have hperturb : (1 + s ^ d / Real.log D) ^ s ≤ 64 := by
    calc
      (1 + s ^ d / Real.log D) ^ s ≤ (2 : ℝ) ^ s :=
        Real.rpow_le_rpow hbase0 (by linarith) hs0
      _ ≤ (2 : ℝ) ^ (6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hshi
      _ = 64 := by norm_num
  have hweighted : weightedHat H .plus s ≤ 1 := by
    by_cases hs3 : s ≤ 3
    · rw [hH.initial_plus s (by linarith) (by norm_num; linarith)]
      norm_num
    · have h3s : 3 < s := lt_of_not_ge hs3
      have hanti : AntitoneOn (weightedHat H .plus) (Icc (3 : ℝ) s) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc (3 : ℝ) s)
        · exact (continuousOn_id.pow 2).mul (hH.continuous .plus) |>.mono (by
            intro x hx
            change 0 < x
            linarith [hx.1])
        · intro x hx
          have hx' : x ∈ Ioo (3 : ℝ) s := by simpa only [interior_Icc] using hx
          exact (hH.dde .plus x (by
            simp [ErrorSign.epsilon]
            linarith [hx'.1])).differentiableAt.differentiableWithinAt
        · intro x hx
          have hx' : x ∈ Ioo (3 : ℝ) s := by simpa only [interior_Icc] using hx
          rw [(hH.dde .plus x (by
            simp [ErrorSign.epsilon]
            linarith [hx'.1])).deriv]
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx'.1])
            (hH.positive .minus (x - 1) (by linarith [hx'.1])).le
      have hle := hanti ⟨le_rfl, h3s.le⟩ ⟨h3s.le, le_rfl⟩ h3s.le
      rw [hH.initial_plus 3 (by norm_num) (by norm_num)] at hle
      norm_num at hle ⊢
      exact hle
  have hT : 0 ≤ H.Tplus s := (hH.positive .plus s (by linarith)).le
  have hsT : s * H.Tplus s ≤ 1 := by
    have hw : s ^ 2 * H.Tplus s ≤ 1 := by
      simpa [weightedHat, Section13HatLayers.T] using hweighted
    nlinarith
  rw [errorEnvelope_odd hN]
  calc
    (1 + s ^ d / Real.log D) ^ s * s * H.Tplus s =
        (1 + s ^ d / Real.log D) ^ s * (s * H.Tplus s) := by ring
    _ ≤ 64 * 1 := mul_le_mul hperturb hsT (mul_nonneg hs0 hT) (by norm_num)
    _ = 64 := by norm_num

-- Both the moving coordinate and the adaptive odd depth follow the same threshold.
private theorem UpperDensitySix_eventually_all_odd_depth_error
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {C K d δ ρ : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d) (hδ : 0 < δ)
    (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ N : ℕ, Odd N → ∀ s : ℝ,
      3 / 2 ≤ s → s ≤ 6 →
      0 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-δ) ∧
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-δ) < ρ := by
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop
  let A : ℝ := C * Real.exp (Real.sqrt K) * 64
  have hsmall : ∀ᶠ D : ℝ in atTop, A * (Real.log D) ^ (-δ) < ρ := by
    have hmul : Tendsto (fun D : ℝ => A * (Real.log D) ^ (-δ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).mul hdecay)
    exact (tendsto_order.1 hmul).2 ρ hρ
  have hlargeLog : ∀ᶠ D : ℝ in atTop, (6 : ℝ) ^ d ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((6 : ℝ) ^ d))
  filter_upwards [hsmall, hlargeLog, eventually_gt_atTop (1 : ℝ)] with D hsmallD hlogD hD
  intro N hN s hslo hshi
  have hE :=
    UpperDensitySix_errorEnvelope_odd_le_sixtyFour H hH hN hd hD hlogD hslo hshi
  have hE0 : 0 ≤ errorEnvelope H N D d s :=
    errorEnvelope_nonneg H N hD (by linarith)
      (hH.positive (ErrorSign.ofDepth N) s (by linarith)).le
  have hlog0 : 0 ≤ Real.log D := (Real.log_pos hD).le
  have hdecay0 : 0 ≤ (Real.log D) ^ (-δ) := Real.rpow_nonneg hlog0 _
  constructor
  · positivity
  · calc
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-δ) ≤ A * (Real.log D) ^ (-δ) := by
            apply mul_le_mul_of_nonneg_right _ hdecay0
            dsimp [A]
            exact mul_le_mul_of_nonneg_left hE
              (mul_nonneg hC (Real.exp_pos _).le)
      _ < ρ := hsmallD

-- The natural-ceiling consumer needs no fixed upper bound on s.
private theorem UpperDensitySix_at_natCeil_of_allDepth
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (S : BoundingSieve)
    {C K d δ : ℝ} (hall : ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d δ N 2)
    (D : ℕ) (s : ℝ)
    (hD : 2 ≤ D) (hslo : 3 / 2 ≤ s)
    (hsSigma : s ≤ sourceSigma (D : ℝ) d)
    (hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-δ)) := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let m : ℕ := S.prodPrimes.primeFactors.card
  let N : ℕ := 2 * m + 1
  have hNodd : Odd N := by dsimp [N]; exact ⟨m, by omega⟩
  have hN1 : 1 ≤ N := by dsimp [N]; omega
  have hsdom : s ∈ KappaOneModel.parityDomain 2 N := by
    simp [KappaOneModel.parityDomain, Nat.odd_iff.mp hNodd]
    linarith
  have hSuzuki := hall N hN1 D (by omega) hD s hsdom hsSigma hz2
  have hfinite := finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    H hH m (by linarith : 1 < s)
  have hVeq : suzukiVProduct S (z : ℝ) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold suzukiVProduct
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, by simpa [z] using hcut p hp⟩
  have hzD : z ≤ D := by
    apply Nat.ceil_le.mpr
    have hbase : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 1 / s ≤ (1 : ℝ) := by
      rw [div_le_one (by linarith : 0 < s)]
      linarith
    simpa [z] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact lt_of_lt_of_le (hcut p hp) hzD
  have hexact := mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    S D z (by omega) hlevel (by simpa [z] using hcut)
  dsimp only [N, m, z] at hSuzuki hexact ⊢
  rw [hVeq] at hSuzuki
  have hprod : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hVeq]
    exact (suzukiVProduct_pos S (z : ℝ)).le
  calc
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) =
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          suzukiActualT S
            (2 * S.prodPrimes.primeFactors.card + 1) D z := by
              simpa [z] using hexact
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (finiteSourceLayer 1 2
              (2 * S.prodPrimes.primeFactors.card + 1) s +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H
                (2 * S.prodPrimes.primeFactors.card + 1)
                (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-δ)) := by
          gcongr
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-δ)) := by
          have hf := hfinite
          dsimp [m] at hf
          nlinarith

/-- The genuine source upper factor bounds the actual upper Rosser main sum
uniformly on `[3/2,6]`, with no residual analytic source hypothesis. -/
theorem goldbach_upperRosserDensity_six :
    ∀ K ρ : ℝ, 1 < K → 0 < ρ →
      ∃ z₀ : ℝ, ∀ S : BoundingSieve, ∀ z Δ s : ℝ,
        z₀ ≤ z → 2 ≤ z → 0 < Δ →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 6 →
        S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
          (suzukiContinuousUpperFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, _hC1min, hall⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨C145, Clow, C, _hC145, _hClow, hC3, hdepth⟩ := hall C1min le_rfl
  intro K ρ _hK hρ
  let K' : ℝ := max 2 K
  have hK' : 2 ≤ K' := le_max_left _ _
  have hKK' : K ≤ K' := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨Dσ, _hDσ1, hDσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) 6 (by norm_num)
  have herrEv := UpperDensitySix_eventually_all_odd_depth_error
    jr1965Section13HatLayers jr1965Section13HatSourceContract.toSection13HatContract
    (C := C) (K := K') (d := 16) (δ := 1 / 2) (ρ := ρ)
      hC0 (by norm_num) (by norm_num) hρ
  obtain ⟨DE, hDE⟩ := eventually_atTop.1 herrEv
  let z₀ : ℝ := max 2 (max Dσ DE)
  refine ⟨z₀, ?_⟩
  intro S z Δ s hz₀ hz2 hΔ hlocal hcut hs hslo hshi
  have hzσ : Dσ ≤ z :=
    (le_max_left Dσ DE).trans ((le_max_right 2 (max Dσ DE)).trans hz₀)
  have hzE : DE ≤ z :=
    (le_max_right Dσ DE).trans ((le_max_right 2 (max Dσ DE)).trans hz₀)
  let D : ℕ := Nat.floor Δ + 1
  have hgeom := real_level_to_natCeil_geometry hz2 hΔ hs hslo
  dsimp only at hgeom
  have hD2 : 2 ≤ D := by simpa [D] using hgeom.1
  have hzroot : z < (D : ℝ) ^ (1 / s) := by simpa [D] using hgeom.2.2.1
  have hzceil : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ := by simpa [D] using hgeom.2.2.2
  have hzD : z < (D : ℝ) := by
    have hbase : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 1 / s ≤ (1 : ℝ) := by
      rw [div_le_one (by linarith : 0 < s)]
      linarith
    have hrootD : (D : ℝ) ^ (1 / s) ≤ D := by
      simpa using Real.rpow_le_rpow_of_exponent_le hbase hexp
    exact hzroot.trans_le hrootD
  have hσ : 6 ≤ sourceSigma (D : ℝ) 16 := hDσ _ (hzσ.trans hzD.le)
  have hsσ : s ≤ sourceSigma (D : ℝ) 16 := hshi.trans hσ
  have hcutCeil : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / s)⌉₊ := by
    intro p hp
    exact Nat.lt_ceil.mpr ((hcut p hp).trans_lt hzroot)
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono hlocal hKK'
  have hmain := UpperDensitySix_at_natCeil_of_allDepth
    jr1965Section13HatLayers jr1965Section13HatSourceContract S
    (hdepth S K' hK' hlocal') D s hD2 hslo hsσ hzceil hcutCeil
  let N : ℕ := 2 * S.prodPrimes.primeFactors.card + 1
  have hNodd : Odd N := ⟨S.prodPrimes.primeFactors.card, by rfl⟩
  have herr := hDE (D : ℝ) (hzE.trans hzD.le) N hNodd s hslo hshi
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact sub_nonneg.mpr
      (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpDvd).le
  dsimp only [D] at hmain ⊢
  dsimp only [N, D] at herr
  calc
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s + ρ) :=
      hmain.trans (mul_le_mul_of_nonneg_left (by linarith [herr.2]) hV0)
    _ = _ := mul_comm _ _

#check goldbach_upperRosserDensity_six
#print axioms goldbach_upperRosserDensity_six

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig