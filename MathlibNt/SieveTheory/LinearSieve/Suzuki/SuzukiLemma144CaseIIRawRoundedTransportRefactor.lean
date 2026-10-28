import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144RecursiveCoordinateSourceSigma
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeilClosed

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

/-!
# Case-II raw rounded transport without the outer-endpoint Claim 14.6(i) interface

The three variants below replace the overstrong quotient Claim-14.6(i) premise
on the outer source interval by the only consequence used by the rounded
assembly: coordinate-wise transport of the quotient error envelope.
-/

theorem caseII_endpoint_le_concrete_finiteSourceLayer_add_qD_natCeil_of_errorTransport
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y : ℕ} {β σ C C1 K ΘK Δ d B0 : ℝ}
    (hH : Section13HatContract H β)
    (hN : Odd N) (hN2 : 2 ≤ N)
    (hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D)
    (hyceil : y = ⌈(D : ℝ) ^ (1 / (β + 1))⌉₊)
    (_hyDhalf : (y : ℝ) ≤ (D : ℝ) / 2)
    (hβ1σ : β + 1 ≤ σ)
    (hD : 1 < (D : ℝ))
    (hDlarge : β * Real.log 2 ≤ (β - 1) * Real.log (D : ℝ))
    (hwy : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / (β + 1)))
    (hy2 : 2 ≤ (y : ℝ))
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / (β + 1)))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hEndpoint : Claim14_5Regime β (D : ℝ) σ C1 K ΘK σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤ B0)
    (hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ (β + 1),
      0 ≤ S.nu p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ (β + 1),
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hSourceDomain : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ (β + 1),
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1))
    (hErrorTransport : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ (β + 1),
      errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (recursiveCoordinate D p) ≤
        errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p))
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      β C K Δ N D σ (β + 1))
    (hErrorThreshold : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ β + 1)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hClaim14_6_ii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hΔ : 0 ≤ Δ)
    (hCeilFull : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (β + 1)) → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (β + 1)) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (hClaim14_13 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (β + 1)) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
      B0 +
        (suzukiVProduct S y *
            (finiteSourceLayer 1 β N (β + 1) +
              (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) β /
                Real.log ((D : ℝ) ^ (1 / σ))) * ((β + 1) / (β + 1))) +
          C * Real.exp (Real.sqrt K) * suzukiVProduct S y *
            (Real.log (D : ℝ)) ^ (-Δ) *
            ((1 / (β + 1)) * (∫ t in (β + 1)..σ,
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
              (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
                  (D : ℝ) d Δ (β + 1) /
                Real.log ((D : ℝ) ^ (1 / σ))) *
                  ((β + 1) / (β + 1)))) := by
  classical
  let s : ℝ := β + 1
  let r : ℝ := (D : ℝ) ^ (1 / s)
  let support := suzukiSupportedBelow S y
  let Tsrc : ℕ → ℕ → ℕ → ℝ := fun n D' p =>
    ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p
  have hτ : caseITau (D : ℝ) s = s :=
    caseITau_eq_beta_add_one_of_log_threshold hH.beta_gt_one hD hDlarge
  have hry : r ≤ (y : ℝ) :=
    (Nat.le_ceil r).trans_eq (congrArg Nat.cast hyceil).symm
  have hsdom : s ∈ KappaOneModel.parityDomain β N := by
    simp only [KappaOneModel.parityDomain, Nat.odd_iff.mp hN, if_pos, Set.mem_Ioi]
    dsimp [s]
    linarith
  have hNm1mod : (N - 1) % 2 = 0 := by
    have hmod := Nat.odd_iff.mp hN
    omega
  have hsm1dom : s - 1 ∈ KappaOneModel.parityDomain β (N - 1) := by
    simp [KappaOneModel.parityDomain, hNm1mod, s]

  -- The middle carrier already contains both real endpoint inequalities.
  have hSource : ∀ p ∈ sigmaOneCarrier support D σ s,
      finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpw, hpr⟩
    have hceil := hCeilFull p (Finset.mem_filter.mp hpSupport).1 hpw hpr
    exact finiteSourceLayer_recursive_le_inherited hH.beta_gt_one (N - 1) D p
      hceil.1 hceil.2 (hSourceDomain p hp).1 (hSourceDomain p hp).2
  have hIHsource := naturalCeilContract_to_sourceCoordinate support Tsrc
    (fun p => suzukiVProduct S p)
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    β C K Δ N D σ s (fun p _ => (suzukiVProduct_pos S (p : ℝ)).le)
    hC hlog hSource hErrorTransport hIH
  have h14 := equation14_10_finset_assembly support S.nu
    (fun p => suzukiVProduct S p) Tsrc
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S y) β C K Δ N D σ s
    (ne_of_gt (suzukiVProduct_pos S y)) hnu hIHsource
  have hMiddle :=
    sigmaEleven_add_sigmaTwelve_suzukiVProduct_le_finiteSourceLayer_add_qD_natCeil_closed
      (S := S) (H := H) (β := β) (C := C) (K := K) (d := d) (Δ := Δ)
      (s := s) (τ := s) (σ := σ) (N := N) (D := D) (z := y)
      hH hsdom hsm1dom le_rfl hβ1σ hD hy2 hroot2 hroot2 hw2
      hwy le_rfl hyceil hErrorThreshold hK hlocal hClaim14_6_ii hC hΔ
      hCeilFull hT hClaim14_13
  -- Transport the carrier, rather than restating the entire middle bound.
  rw [← sigmaTwelve_supportedBelow_eq_full S
    (fun p => suzukiVProduct S p)
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S y) C K Δ N D y σ s hry] at hMiddle

  -- Split once at the lower cutoff; natural ceiling preserves strict cutoffs.
  have hLow : support.filter (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)) =
      suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊ := by
    dsimp [support]
    rw [hyceil, suzukiSupportedBelow_ceil_real, suzukiSupportedBelow_ceil_real,
      Finset.filter_filter]
    exact Finset.filter_congr fun p _ =>
      ⟨And.right, fun hp => ⟨hp.trans_le hwy, hp⟩⟩
  have hHigh : support.filter (fun p : ℕ => ¬ (p : ℝ) < (D : ℝ) ^ (1 / σ)) =
      sigmaOneCarrier support D σ s := by
    apply Finset.filter_congr
    intro p hp
    have hpr := (nat_lt_of_eq_ceil_iff hyceil).mp (Finset.mem_filter.mp hp).2
    exact ⟨fun hpw => ⟨le_of_not_gt hpw, hpr⟩, fun hpw => not_lt.mpr hpw.1⟩
  rw [suzukiSourceParitySum_recurrence_of_odd_of_supported_cube S hN hycube,
    ← Finset.sum_filter_add_sum_filter_not support
      (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)), hLow, hHigh]
  apply add_le_add (hEndpoint (claim14_5_sigma_endpoint_regime (by linarith)))
  change sigmaOne support S.nu Tsrc N D σ s ≤ _
  simpa [s] using h14.trans hMiddle

/-- Double-rounded sharp Case-II endpoint transport.

The natural cutoffs are `y = ceil(D^(1/3))` and `z = ceil(D^(1/s))`.
Dimension-one transport and the logarithmic ratio are carried out only at the
exact real roots.  The two Euler products are then returned exactly to their
natural-ceiling cutoffs; no equality between a cast natural cutoff and a real
root is assumed. -/
theorem caseII_total_le_from_caseI_endpoint_explicit_rawBase_natCeil_of_errorTransport
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {σ C C1 K ΘK Δ d B0 s : ℝ}
    (hH : Section13HatContract H 2)
    (hN : Odd N) (hN2 : 2 ≤ N)
    (hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D)
    (hyceil : y = ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
    (hyDhalf : (y : ℝ) ≤ (D : ℝ) / 2)
    (h3σ : 3 ≤ σ)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hDlarge : 2 * Real.log 2 ≤ Real.log (D : ℝ))
    (hwy : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / (3 : ℝ)))
    (hy2 : 2 ≤ (y : ℝ))
    (hyr2 : 2 ≤ (D : ℝ) ^ (1 / (3 : ℝ)))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hEndpoint : Claim14_5Regime 2 (D : ℝ) σ C1 K ΘK σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤ B0)
    (hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ S.nu p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hSourceDomain : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ 3,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1))
    (hErrorTransport : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ 3,
      errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (recursiveCoordinate D p) ≤
        errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p))
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ 3)
    (hErrorThreshold : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ 3)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hClaim14_6_ii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hΔ0 : 0 ≤ Δ)
    (hCeilFull : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (hClaim14_13 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ)))
    (hs : 0 < s) (hs3 : s ≤ 3)
    (hyrzr : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (D : ℝ) ^ (1 / s))
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hzr2 : 2 ≤ (D : ℝ) ^ (1 / s)) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
        caseIIRoundedTransportErr S H N (D : ℝ)
          ((D : ℝ) ^ (1 / (3 : ℝ))) ((D : ℝ) ^ (1 / s))
          d Δ σ C K B0 s +
        suzukiVProduct S (z : ℝ) * (9 * K / (s * Real.log (D : ℝ))) := by
  let yr : ℝ := (D : ℝ) ^ (1 / (3 : ℝ))
  let zr : ℝ := (D : ℝ) ^ (1 / s)
  have hDone : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
  have hF : 0 ≤ finiteSourceLayer 1 2 N 3 :=
    caseII_finiteSourceLayer_three_nonneg hN
  have hSigma11 : 0 ≤ caseIIEndpointSigma11 K N (D : ℝ) σ :=
    caseIIEndpointSigma11_nonneg hN hw2
  have hQD : 0 ≤ caseIIEndpointQD H N (D : ℝ) d Δ σ C K :=
    caseIIEndpointQD_nonneg hH hDone h3σ hw2 hC
  have hcaseIRaw :=
    caseII_endpoint_le_concrete_finiteSourceLayer_add_qD_natCeil_of_errorTransport
      (S := S) (H := H) (N := N) (D := D) (y := y)
      (β := (2 : ℝ)) (σ := σ) (C := C) (C1 := C1) (K := K)
      (ΘK := ΘK) (Δ := Δ) (d := d) (B0 := B0)
      hH hN hN2 hycube (by convert hyceil using 1; norm_num) hyDhalf
      (by norm_num at h3σ ⊢; exact h3σ) hDone
      (by norm_num at hDlarge ⊢; exact hDlarge)
      (by convert hwy using 1; norm_num) hy2
      (by convert hyr2 using 1; norm_num) hw2 hEndpoint
      (by norm_num at hnu ⊢; exact hnu) hC
      (by norm_num at hlog ⊢; exact hlog)
      (by norm_num at hSourceDomain ⊢; exact hSourceDomain)
      (by norm_num at hErrorTransport ⊢; exact hErrorTransport)
      (by norm_num at hIH ⊢; exact hIH)
      (by norm_num at hErrorThreshold ⊢; exact hErrorThreshold) hK hlocal
      hClaim14_6_ii hΔ0
      (by convert hCeilFull using 1; norm_num)
      (by convert hT using 1; norm_num)
      (by convert hClaim14_13 using 1; norm_num)
  have hVy : suzukiVProduct S (y : ℝ) = suzukiVProduct S yr := by
    exact suzukiVProduct_natCeil_eq S (by simpa [yr] using hyceil)
  have hVz : suzukiVProduct S (z : ℝ) = suzukiVProduct S zr := by
    exact suzukiVProduct_natCeil_eq S (by simpa [zr] using hzceil)
  have hcaseI :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        B0 + suzukiVProduct S yr *
          (finiteSourceLayer 1 2 N 3 + caseIIEndpointSigma11 K N (D : ℝ) σ) +
          suzukiVProduct S yr * caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
    rw [← hVy]
    convert hcaseIRaw using 1;
      simp only [caseIIEndpointSigma11, caseIIEndpointQD]; ring
  have hVratio : suzukiVProduct S yr ≤
      suzukiVProduct S zr * (Real.log zr / Real.log yr) *
        (1 + K / Real.log yr) := by
    have hratio := hlocal yr zr (by simpa [yr] using hyr2)
      (by simpa [yr, zr] using hyrzr)
    have hprod : suzukiVProduct S yr =
        suzukiVProduct S zr * suzukiLocalRatio S yr zr := by
      classical
      let A := S.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < yr)
      let B := S.prodPrimes.primeFactors.filter
        (fun p : ℕ => yr ≤ (p : ℝ) ∧ (p : ℝ) < zr)
      let Cset := S.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < zr)
      have hdisj : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro p hpA hpB
        simp only [A, B, mem_filter] at hpA hpB
        linarith [hpA.2, hpB.2.1]
      have hunion : A ∪ B = Cset := by
        ext p
        simp only [A, B, Cset, Finset.mem_union, mem_filter]
        constructor
        · rintro (hpA | hpB)
          · exact ⟨hpA.1, hpA.2.trans_le (by simpa [yr, zr] using hyrzr)⟩
          · exact ⟨hpB.1, hpB.2.2⟩
        · intro hpC
          by_cases hp : (p : ℝ) < yr
          · exact Or.inl ⟨hpC.1, hp⟩
          · exact Or.inr ⟨hpC.1, le_of_not_gt hp, hpC.2⟩
      have hBne : (∏ p ∈ B, (1 - S.nu p)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro p hp
        have hpP : p ∈ S.prodPrimes.primeFactors :=
          (mem_filter.mp hp).1
        exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p
          (Nat.prime_of_mem_primeFactors hpP)
          (Nat.mem_primeFactors.mp hpP).2.1))
      unfold suzukiVProduct suzukiLocalRatio
      change (∏ p ∈ A, (1 - S.nu p)) =
        (∏ p ∈ Cset, (1 - S.nu p)) *
          ∏ p ∈ B, (1 - S.nu p)⁻¹
      rw [← hunion, Finset.prod_union hdisj]
      rw [Finset.prod_inv_distrib]
      field_simp [hBne]
    rw [hprod]
    simpa [suzukiLocalRatio, mul_assoc] using
      (mul_le_mul_of_nonneg_left hratio (suzukiVProduct_pos S zr).le)
  have hlogRatio : Real.log zr / Real.log yr = 3 / s := by
    exact caseII_log_ratio_of_power_identities
      (D := (D : ℝ)) (y := yr) (z := zr) hD hs (by simp [yr]) (by simp [zr])
  rw [hlogRatio] at hVratio
  have hmain := mul_le_mul_of_nonneg_right hVratio hF
  have h11 := mul_le_mul_of_nonneg_right hVratio hSigma11
  have hq := mul_le_mul_of_nonneg_right hVratio hQD
  have hendpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S zr * ((3 / s) * finiteSourceLayer 1 2 N 3) +
          caseIIRoundedTransportErr S H N (D : ℝ) yr zr
            d Δ σ C K B0 s := by
    unfold caseIIRoundedTransportErr
    calc
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
          B0 + suzukiVProduct S yr * finiteSourceLayer 1 2 N 3 +
            suzukiVProduct S yr * caseIIEndpointSigma11 K N (D : ℝ) σ +
            suzukiVProduct S yr *
              caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
        nlinarith [hcaseI]
      _ ≤ B0 +
          (suzukiVProduct S zr * (3 / s) *
            (1 + K / Real.log yr)) * finiteSourceLayer 1 2 N 3 +
          (suzukiVProduct S zr * (3 / s) *
            (1 + K / Real.log yr)) * caseIIEndpointSigma11 K N (D : ℝ) σ +
          (suzukiVProduct S zr * (3 / s) *
            (1 + K / Real.log yr)) *
              caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
        gcongr
      _ = suzukiVProduct S zr * ((3 / s) * finiteSourceLayer 1 2 N 3) +
          (B0 + suzukiVProduct S zr *
            ((3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 +
              (3 / s) * (1 + K / Real.log yr) *
                caseIIEndpointSigma11 K N (D : ℝ) σ +
              (3 / s) * (1 + K / Real.log yr) *
                caseIIEndpointQD H N (D : ℝ) d Δ σ C K)) := by ring
  have hfinal := caseII_total_le_concrete_finiteSourceLayer_add_rawBase_natCeil
    S hN hD hs hs3 (by linarith) hyz hyLower hyUpper hzceil hzr2 hlocal hendpoint
  simpa [yr, zr] using hfinal


end MathlibNt.SieveTheory
