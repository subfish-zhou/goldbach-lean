import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144LiteralAllDepthUniformInS
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityProducer
import MathlibNt.SieveTheory.UpperRosserSuzukiExactBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaElementaryHead

open Set Filter Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

noncomputable section

/-- On the compact upper-sieve window the odd Suzuki error envelope has a
bound independent of the (possibly carrier-adaptive) depth. -/
theorem errorEnvelope_odd_le_sixteen_on_upper_window
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {N : ℕ} (hN : Odd N) {D d s : ℝ}
    (hd : 0 ≤ d) (hD : 1 < D) (hlog : 4 ^ d ≤ Real.log D)
    (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    errorEnvelope H N D d s ≤ 16 := by
  have hs0 : 0 ≤ s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hsd : s ^ d ≤ (4 : ℝ) ^ d :=
    Real.rpow_le_rpow hs0 (by linarith) hd
  have hlogpos : 0 < Real.log D := Real.log_pos hD
  have hratio : s ^ d / Real.log D ≤ 1 :=
    (div_le_one hlogpos).2 (hsd.trans hlog)
  have hbase0 : 0 ≤ 1 + s ^ d / Real.log D := by positivity
  have hperturb : (1 + s ^ d / Real.log D) ^ s ≤ 16 := by
    calc
      (1 + s ^ d / Real.log D) ^ s ≤ (2 : ℝ) ^ s :=
        Real.rpow_le_rpow hbase0 (by linarith) hs0
      _ ≤ (2 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hshi
      _ = 16 := by norm_num
  have hweighted_nonneg : 0 ≤ weightedHat H .plus s := by
    unfold weightedHat
    exact mul_nonneg (sq_nonneg s) (hH.positive .plus s (by linarith)).le
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
  have hT : 0 ≤ H.Tplus s := by
    exact (hH.positive .plus s (by linarith)).le
  have hsT : s * H.Tplus s ≤ 1 := by
    have hw : s ^ 2 * H.Tplus s ≤ 1 := by
      simpa [weightedHat, Section13HatLayers.T] using hweighted
    nlinarith
  rw [errorEnvelope_odd hN]
  calc
    (1 + s ^ d / Real.log D) ^ s * s * H.Tplus s =
        (1 + s ^ d / Real.log D) ^ s * (s * H.Tplus s) := by ring
    _ ≤ 16 * 1 := mul_le_mul hperturb hsT (mul_nonneg hs0 hT) (by norm_num)
    _ = 16 := by norm_num

/-- Uniform scalar absorption on `[3/2,4]`, simultaneously for every odd
adaptive depth.  The depth enters the literal error only through its parity. -/
theorem eventually_all_odd_depth_suzuki_error_upper_window
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {C K d Δ ρ : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d) (hΔ : 0 < Δ)
    (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ N : ℕ, Odd N → ∀ s : ℝ,
      3 / 2 ≤ s → s ≤ 4 →
      0 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) ∧
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) < ρ := by
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-Δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hΔ).comp Real.tendsto_log_atTop
  let A : ℝ := C * Real.exp (Real.sqrt K) * 16
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsmall : ∀ᶠ D : ℝ in atTop, A * (Real.log D) ^ (-Δ) < ρ := by
    have hmul : Tendsto (fun D : ℝ => A * (Real.log D) ^ (-Δ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).mul hdecay)
    exact (tendsto_order.1 hmul).2 ρ hρ
  have hlargeLog : ∀ᶠ D : ℝ in atTop, (4 : ℝ) ^ d ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((4 : ℝ) ^ d))
  filter_upwards [hsmall, hlargeLog, eventually_gt_atTop (1 : ℝ)] with D hsmallD hlogD hD
  intro N hN s hslo hshi
  have hE := errorEnvelope_odd_le_sixteen_on_upper_window H hH hN hd hD hlogD hslo hshi
  have hE0 : 0 ≤ errorEnvelope H N D d s :=
    errorEnvelope_nonneg H N hD (by linarith)
      (hH.positive (ErrorSign.ofDepth N) s (by linarith)).le
  have hlog0 : 0 ≤ Real.log D := (Real.log_pos hD).le
  have hdecay0 : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlog0 _
  constructor
  · positivity
  · calc
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) ≤ A * (Real.log D) ^ (-Δ) := by
            apply mul_le_mul_of_nonneg_right _ hdecay0
            dsimp [A]
            exact mul_le_mul_of_nonneg_left hE
              (mul_nonneg hC (Real.exp_pos _).le)
      _ < ρ := hsmallD

/-- Odd finite source layers are exactly the initial segment used by Suzuki's
continuous upper source factor. -/
theorem finiteSourceLayer_two_mul_add_one_eq_sum_oddLayers
    (m : ℕ) (s : ℝ) :
    finiteSourceLayer 1 2 (2 * m + 1) s =
      ∑ k ∈ Finset.range (m + 1), suzukiLayer 1 2 (2 * k + 1) s := by
  classical
  have hcarrier :
      (Finset.Icc 1 (2 * m + 1)).filter (fun n => n % 2 = 1) =
        (Finset.range (m + 1)).image (fun k => 2 * k + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hn1, hnm⟩, hnOdd⟩
      refine ⟨n / 2, ?_, ?_⟩ <;> omega
    · rintro ⟨k, hk, rfl⟩
      constructor <;> omega
  unfold finiteSourceLayer
  rw [show (2 * m + 1) % 2 = 1 by omega]
  rw [← Finset.sum_filter, hcarrier, Finset.sum_image]
  intro a ha b hb hab
  change 2 * a + 1 = 2 * b + 1 at hab
  omega

/-- Every carrier-adaptive odd finite source factor lies below the genuine
continuous upper source factor. -/
theorem finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (m : ℕ) {s : ℝ} (hs : 1 < s) :
    finiteSourceLayer 1 2 (2 * m + 1) s ≤
      suzukiContinuousUpperFactor s - 1 := by
  rw [finiteSourceLayer_two_mul_add_one_eq_sum_oddLayers]
  unfold suzukiContinuousUpperFactor suzukiProposition118SourceTPlus
  have hsum := summable_suzukiProposition118SourceTPlus_of_sourceContract hH hs
  linarith [hsum.sum_le_tsum (Finset.range (m + 1))
    (fun k hk => suzukiLayer_one_two_odd_nonneg hs k)]

/-- Complete direct consumer at a natural Suzuki coordinate.  The exact finite
upper-Rosser/Suzuki bridge is invoked internally; no bridge premise or uniform
ordered-layer tail is assumed. -/
theorem upperRosserDensity_at_natCeil_of_allDepth
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (S : BoundingSieve)
    {C K d Δ : ℝ} (hall : ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2)
    (D : ℕ) (s : ℝ)
    (hD : 2 ≤ D) (hslo : 3 / 2 ≤ s) (_hshi : s ≤ 4)
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
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
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
  have hexact := upperRosserSuzukiExactBridge S D z (by omega) hlevel
    (by simpa [z] using hcut)
  dsimp only [N, m, z] at hSuzuki hexact ⊢
  rw [hVeq] at hSuzuki
  have hprod : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hVeq]
    exact (suzukiVProduct_pos S (z : ℝ)).le
  calc
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
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
                (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          gcongr
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          have hf := hfinite
          dsimp [m] at hf
          nlinarith

/-- Production wrapper: the all-depth Suzuki producer feeds the direct odd-depth
consumer with constants selected before the bounding sieve.  The exact bridge
is a proved internal dependency, not a proposition-valued premise. -/
theorem exists_upperRosserDensity_at_natCeil_of_suzuki_allDepth
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ (S : BoundingSieve) (K : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ D : ℕ, 2 ≤ D → ∀ s : ℝ,
              3 / 2 ≤ s → s ≤ 4 → s ≤ sourceSigma (D : ℝ) d →
              2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
              (∀ p ∈ S.prodPrimes.primeFactors,
                p < ⌈(D : ℝ) ^ (1 / s)⌉₊) →
              S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
                  (suzukiContinuousUpperFactor s +
                    C * Real.exp (Real.sqrt K) *
                      errorEnvelope H
                        (2 * S.prodPrimes.primeFactors.card + 1)
                        (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  obtain ⟨C1min, hC1min, hall⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hdepth⟩ := hall C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro S K hK hlocal D hD s hslo hshi hsSigma hz2 hcut
  exact upperRosserDensity_at_natCeil_of_allDepth H hH S
    (hdepth S K hK hlocal) D s hD hslo hshi hsSigma hz2 hcut


end
end MathlibNt.SieveTheory
