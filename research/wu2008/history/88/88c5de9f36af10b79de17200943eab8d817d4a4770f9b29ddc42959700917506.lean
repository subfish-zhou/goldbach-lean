import MathlibNt.Wu2008DoubleSieve.CanonicalBoundedFactors

/-!
# Actual bounded-domain canonical Rosser density

The error threshold works simultaneously for every legal parity and every
coordinate through ten, before the sieve or its carrier-adaptive depth is
chosen. The upper finite bridge is used directly, avoiding the frozen wrapper's
unneeded restriction to four. The moving source restriction is paid uniformly
by a fixed threshold for `10 ≤ sourceSigma D 16`.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Topology
open scoped Classical BigOperators
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

private theorem bounded_perturbation {D d s : ℝ}
    (hd : 0 ≤ d) (hD : 1 < D) (hlog : 10 ^ d ≤ Real.log D)
    (hs : 0 ≤ s) (hs10 : s ≤ 10) :
    (1 + s ^ d / Real.log D) ^ s ≤ 1024 := by
  have hlogpos : 0 < Real.log D := Real.log_pos hD
  have hratio : s ^ d / Real.log D ≤ 1 :=
    (div_le_one (Real.log_pos hD)).2
      ((Real.rpow_le_rpow hs hs10 hd).trans hlog)
  calc
    _ ≤ (2 : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity) (by linarith) hs
    _ ≤ (2 : ℝ) ^ (10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hs10
    _ = 1024 := by norm_num

private theorem bounded_minus_hat
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 2 ≤ s) : s * H.Tminus s ≤ 1 := by
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
  have hweighted := hanti ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  rw [hH.initial_minus 2 (by norm_num) le_rfl] at hweighted
  have hT := (hH.positive .minus s (by linarith)).le
  have hw : s ^ 2 * H.Tminus s ≤ 2 := by
    simpa [weightedHat, Section13HatLayers.T] using hweighted
  have hmul := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (by linarith : 0 ≤ s) hT)
  nlinarith

private theorem bounded_plus_hat
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 3 / 2 ≤ s) : s * H.Tplus s ≤ 1 := by
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
  have hT := (hH.positive .plus s (by linarith)).le
  have hw : s ^ 2 * H.Tplus s ≤ 1 := by
    simpa [weightedHat, Section13HatLayers.T] using hweighted
  nlinarith

/-- A depth-independent error envelope bound on both bounded parity domains. -/
theorem errorEnvelope_le_bounded
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {n : ℕ} {D d s : ℝ} (hd : 0 ≤ d) (hD : 1 < D)
    (hlog : 10 ^ d ≤ Real.log D) (hs10 : s ≤ 10)
    (hdom : (Even n ∧ 2 ≤ s) ∨ (Odd n ∧ 3 / 2 ≤ s)) :
    errorEnvelope H n D d s ≤ 1024 := by
  rcases hdom with ⟨hn, hs⟩ | ⟨hn, hs⟩
  · rw [errorEnvelope_even hn]
    have hp := bounded_perturbation hd hD hlog (by linarith : 0 ≤ s) hs10
    have ht := bounded_minus_hat H hH hs
    have ht0 : 0 ≤ s * H.Tminus s :=
      mul_nonneg (by linarith) (hH.positive .minus s (by linarith)).le
    calc
      _ = (1 + s ^ d / Real.log D) ^ s * (s * H.Tminus s) := by ring
      _ ≤ 1024 * 1 := mul_le_mul hp ht ht0 (by norm_num)
      _ = 1024 := by norm_num
  · rw [errorEnvelope_odd hn]
    have hp := bounded_perturbation hd hD hlog (by linarith : 0 ≤ s) hs10
    have ht := bounded_plus_hat H hH hs
    have ht0 : 0 ≤ s * H.Tplus s :=
      mul_nonneg (by linarith) (hH.positive .plus s (by linarith)).le
    calc
      _ = (1 + s ^ d / Real.log D) ^ s * (s * H.Tplus s) := by ring
      _ ≤ 1024 * 1 := mul_le_mul hp ht ht0 (by norm_num)
      _ = 1024 := by norm_num

/-- The threshold is selected before every depth and coordinate, so it can
be consumed at the full, growing carrier depth. -/
theorem eventually_bounded_depth_error_small
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {C K d δ ρ : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d) (hδ : 0 < δ)
    (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ n : ℕ, ∀ s : ℝ, s ≤ 10 →
      ((Even n ∧ 2 ≤ s) ∨ (Odd n ∧ 3 / 2 ≤ s)) →
      C * Real.exp (Real.sqrt K) * errorEnvelope H n D d s *
        (Real.log D) ^ (-δ) < ρ := by
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop
  let A : ℝ := C * Real.exp (Real.sqrt K) * 1024
  have hsmall : ∀ᶠ D : ℝ in atTop, A * (Real.log D) ^ (-δ) < ρ := by
    have hmul : Tendsto (fun D : ℝ => A * (Real.log D) ^ (-δ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hdecay.const_mul A
    exact (tendsto_order.1 hmul).2 ρ hρ
  have hlargeLog : ∀ᶠ D : ℝ in atTop, (10 : ℝ) ^ d ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((10 : ℝ) ^ d))
  filter_upwards [hsmall, hlargeLog, eventually_gt_atTop (1 : ℝ)] with
    D hsmallD hlogD hD
  intro n s hs10 hdom
  have hE := errorEnvelope_le_bounded H hH hd hD hlogD hs10 hdom
  calc
    _ ≤ A * (Real.log D) ^ (-δ) := by
      apply mul_le_mul_of_nonneg_right _
        (Real.rpow_nonneg (Real.log_pos hD).le _)
      exact mul_le_mul_of_nonneg_left hE (mul_nonneg hC (Real.exp_pos _).le)
    _ < ρ := hsmallD

private theorem bounded_upper_natCeil
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (S : BoundingSieve) {C K d δ : ℝ}
    (hall : ∀ n : ℕ, 1 ≤ n → Lemma144MovingDomainNatCeilAt S H C K d δ n 2)
    (D : ℕ) (s : ℝ) (hD : 2 ≤ D) (hs : 3 / 2 ≤ s)
    (hsSigma : s ≤ sourceSigma (D : ℝ) d)
    (hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    S.mainSum (upperRosserWeight S.prodPrimes D) ≤
      sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-δ)) := by
  let Z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let n : ℕ := 2 * S.prodPrimes.primeFactors.card + 1
  have hn : Odd n := ⟨S.prodPrimes.primeFactors.card, rfl⟩
  have hsdom : s ∈ KappaOneModel.parityDomain 2 n := by
    simp [KappaOneModel.parityDomain, Nat.odd_iff.mp hn]
    linarith
  have hSuzuki := hall n (by dsimp [n]; omega) D (by omega) hD s hsdom hsSigma hz2
  have hfinite := finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    H hH S.prodPrimes.primeFactors.card (by linarith : 1 < s)
  have hVeq : suzukiVProduct S (Z : ℝ) = sieveProductPrimeFactors S := by
    unfold suzukiVProduct sieveProductPrimeFactors
    congr 1
    ext p
    simp only [mem_filter]
    exact ⟨fun hp => hp.1, fun hp => ⟨hp, by simpa [Z] using hcut p hp⟩⟩
  have hZD : Z ≤ D := by
    apply Nat.ceil_le.mpr
    have hbase : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 1 / s ≤ (1 : ℝ) := (div_le_one (by linarith)).2 (by linarith)
    simpa [Z] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D :=
    fun p hp => (hcut p hp).trans_le hZD
  have hexact := upperRosserSuzukiExactBridge S D Z (by omega) hlevel hcut
  have hV : 0 ≤ sieveProductPrimeFactors S := by
    rw [← hVeq]
    exact (suzukiVProduct_pos S _).le
  change suzukiActualT S n D Z ≤ suzukiVProduct S (Z : ℝ) *
    (finiteSourceLayer 1 2 n s + C * Real.exp (Real.sqrt K) *
      errorEnvelope H n (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-δ)) at hSuzuki
  rw [hVeq] at hSuzuki
  have hmul := mul_le_mul_of_nonneg_left hfinite hV
  dsimp only [n] at hSuzuki
  nlinarith

/-- Canonical lower density on `[2,10]`, with its actual source coordinate. -/
theorem canonical_lower_density_fundamentalLemma_bounded
    {K ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ (S : BoundingSieve) (z level s : ℝ),
      z0 ≤ z → 2 ≤ z → 0 < level →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log level / Real.log z → 2 ≤ s → s ≤ 10 →
      (jr1965f s - ρ) * sieveProductPrimeFactors S ≤
        S.mainSum (lowerRosserWeight S.prodPrimes (⌊level⌋₊ + 1)) := by
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, _, hall⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_C145, _Clow, C, _, _, hC, hnat⟩ := hall C1min le_rfl
  let K' : ℝ := max 2 K
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨Dσ, _, hDσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) 10 (by norm_num)
  obtain ⟨DE, hDE⟩ := eventually_atTop.1
    (eventually_bounded_depth_error_small jr1965Section13HatLayers
      jr1965Section13HatSourceContract.toSection13HatContract
      (C := C) (K := K') (d := 16) (δ := 1 / 2) hC0
      (by norm_num) (by norm_num) hρ)
  refine ⟨max 2 (max Dσ DE), ?_⟩
  intro S z level s hz0 hz2 hlevel hlocal hcut hs hs2 hs10
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
    hs10.trans (hDσ _ (hzσ.trans hzD.le))
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono hlocal (le_max_right _ _)
  have hcutZ : ∀ p ∈ S.prodPrimes.primeFactors, p < Z :=
    fun p hp => Nat.lt_ceil.mpr ((hcut p hp).trans_lt hroot)
  have hcutD : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact_mod_cast (hcut p hp).trans_lt hzD
  have hmain := hnat S K' (le_max_left _ _) hlocal' D hD2 s hs2 hsσ hZ2
  change suzukiVProduct S (Z : ℝ) *
      (suzukiContinuousLowerFactor s -
        C * Real.exp (Real.sqrt K') * errorEnvelope jr1965Section13HatLayers n
          (D : ℝ) 16 s * (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S Z) at hmain
  have herr := hDE (D : ℝ) (hzE.trans hzD.le) n s hs10
    (Or.inl ⟨even_two_mul _, hs2⟩)
  have hbound : suzukiVProduct S (Z : ℝ) * (jr1965f s - ρ) ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S Z) := by
    rw [suzukiContinuousLowerFactor_eq_jr1965f_bounded hs2 hs10] at hmain
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left herr.le _)
      (suzukiVProduct_pos S _).le).trans hmain
  have hbridge := suzukiDensityProduct_lowerRosserWeight_exact_bridge S D Z hcutZ hcutD
  rw [hbridge.2.1, ← hbridge.1] at hbound
  simpa only [mul_comm] using hbound

/-- Canonical upper density on `[3/2,10]`. Constants precede the actual sieve
and the odd depth selected from all of its prime factors. -/
theorem canonical_upper_density_fundamentalLemma_bounded
    {K ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ (S : BoundingSieve) (z level s : ℝ),
      z0 ≤ z → 2 ≤ z → 0 < level →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log level / Real.log z → 3 / 2 ≤ s → s ≤ 10 →
      S.mainSum (upperRosserWeight S.prodPrimes (⌊level⌋₊ + 1)) ≤
        (jr1965F s + ρ) * sieveProductPrimeFactors S := by
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, _, hall⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_C145, _Clow, C, _, _, hC, hdepth⟩ := hall C1min le_rfl
  let K' : ℝ := max 2 K
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨Dσ, _, hDσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) 10 (by norm_num)
  obtain ⟨DE, hDE⟩ := eventually_atTop.1
    (eventually_bounded_depth_error_small jr1965Section13HatLayers
      jr1965Section13HatSourceContract.toSection13HatContract
      (C := C) (K := K') (d := 16) (δ := 1 / 2) hC0
      (by norm_num) (by norm_num) hρ)
  refine ⟨max 2 (max Dσ DE), ?_⟩
  intro S z level s hz0 hz2 hlevel hlocal hcut hs hslo hs10
  let D : ℕ := ⌊level⌋₊ + 1
  have hgeom := real_level_to_natCeil_geometry hz2 hlevel hs hslo
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
    hs10.trans (hDσ _ (hzσ.trans hzD.le))
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono hlocal (le_max_right _ _)
  have hcutZ : ∀ p ∈ S.prodPrimes.primeFactors, p < ⌈(D : ℝ) ^ (1 / s)⌉₊ :=
    fun p hp => Nat.lt_ceil.mpr ((hcut p hp).trans_lt hgeom.2.2.1)
  have hmain := bounded_upper_natCeil jr1965Section13HatLayers
    jr1965Section13HatSourceContract S (hdepth S K' (le_max_left _ _) hlocal')
    D s hgeom.1 hslo hsσ hgeom.2.2.2 hcutZ
  have herr := hDE (D : ℝ) (hzE.trans hzD.le)
    (2 * S.prodPrimes.primeFactors.card + 1) s hs10
    (Or.inr ⟨⟨S.prodPrimes.primeFactors.card, rfl⟩, hslo⟩)
  rw [suzukiContinuousUpperFactor_eq_jr1965F_bounded (by linarith) hs10] at hmain
  have hV : 0 ≤ sieveProductPrimeFactors S := by
    unfold sieveProductPrimeFactors
    apply prod_nonneg
    intro p hp
    exact sub_nonneg.mpr
      (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)).le
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_left herr.le (jr1965F s)) hV
  exact hmain.trans (by simpa only [mul_comm, add_comm] using hmul)

/-- The actual Goldbach lower main sum, with the local product at `d*N`. -/
theorem ordinaryRosser_lower_density_canonical_bounded_local
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 2 ≤ s → s ≤ 10 →
      (jr1965f s - ρ) * localSieveProduct (d * N) z ≤
        ordinaryRosserMainSum false N d (⌊level⌋₊ + 1) z := by
  obtain ⟨K, _, hdim⟩ := ordinaryGoldbach_uniform_dimension_one
  obtain ⟨z0, hbound⟩ := canonical_lower_density_fundamentalLemma_bounded (K := K) hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hs2 hs10
  have hcut : ∀ p ∈ (ordinaryGoldbachBoundingSieve N d he z).prodPrimes.primeFactors,
      (p : ℝ) ≤ z := by
    change ∀ p ∈ (ordinarySievePrimeProduct (d * N) z).primeFactors, (p : ℝ) ≤ z
    rw [ordinarySievePrimeProduct_primeFactors]
    exact fun _p hp => (mem_primeWindow.mp hp).2.2.2.le
  have h := hbound (ordinaryGoldbachBoundingSieve N d he z) z level s hz0 hz hlevel
    (hdim N d he z) hcut hs hs2 hs10
  rw [ordinaryGoldbach_lower_mainSum_eq, ordinaryGoldbach_sieveProduct_eq_local] at h
  exact h

/-- The actual Goldbach upper main sum, with the local product at `d*N`. -/
theorem ordinaryRosser_upper_density_canonical_bounded_local
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 3 / 2 ≤ s → s ≤ 10 →
      ordinaryRosserMainSum true N d (⌊level⌋₊ + 1) z ≤
        (jr1965F s + ρ) * localSieveProduct (d * N) z := by
  obtain ⟨K, _, hdim⟩ := ordinaryGoldbach_uniform_dimension_one
  obtain ⟨z0, hbound⟩ := canonical_upper_density_fundamentalLemma_bounded (K := K) hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hslo hs10
  have hcut : ∀ p ∈ (ordinaryGoldbachBoundingSieve N d he z).prodPrimes.primeFactors,
      (p : ℝ) ≤ z := by
    change ∀ p ∈ (ordinarySievePrimeProduct (d * N) z).primeFactors, (p : ℝ) ≤ z
    rw [ordinarySievePrimeProduct_primeFactors]
    exact fun _p hp => (mem_primeWindow.mp hp).2.2.2.le
  have h := hbound (ordinaryGoldbachBoundingSieve N d he z) z level s hz0 hz hlevel
    (hdim N d he z) hcut hs hslo hs10
  rw [ordinaryGoldbach_mainSum_eq, ordinaryGoldbach_sieveProduct_eq_local] at h
  exact h

end Wu2008DoubleSieve
