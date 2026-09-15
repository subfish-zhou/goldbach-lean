import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointFromCaseI

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Integer cutoffs below a natural ceiling have exactly the same carrier as the
strict real cutoff. -/
theorem nat_lt_of_eq_ceil_iff {x : ℝ} {z p : ℕ} (hz : z = ⌈x⌉₊) :
    p < z ↔ (p : ℝ) < x := by
  rw [hz, Nat.lt_ceil]

/-- Suzuki's finite Euler product is unchanged when a strict real cutoff is
replaced by its natural ceiling. -/
theorem suzukiVProduct_natCeil_eq
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hz : z = ⌈x⌉₊) :
    suzukiVProduct S (z : ℝ) = suzukiVProduct S x := by
  classical
  unfold suzukiVProduct
  congr 1
  ext p
  simp only [Finset.mem_filter]
  rw [Nat.cast_lt]
  rw [nat_lt_of_eq_ceil_iff hz]

/-- The Lemma-8.7 prime sum is likewise insensitive to replacing its Euler
suffix cutoff by the natural ceiling. -/
theorem suzukiLemmaEightSevenPrimeSum_natCeil_eq
    (S : BoundingSieve) (D w v x : ℝ) (F : ℝ → ℝ)
    {z : ℕ} (hz : z = ⌈x⌉₊) :
    suzukiLemmaEightSevenPrimeSum S D w v (z : ℝ) F =
      suzukiLemmaEightSevenPrimeSum S D w v x F := by
  classical
  unfold suzukiLemmaEightSevenPrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  have hfilter :
      S.prodPrimes.primeFactors.filter
          (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (z : ℝ)) =
        S.prodPrimes.primeFactors.filter
          (fun q : ℕ => p ≤ q ∧ (q : ℝ) < x) := by
    ext q
    simp only [Finset.mem_filter]
    rw [Nat.cast_lt, nat_lt_of_eq_ceil_iff hz]
  rw [hfilter]

/-- Rounded version of the concrete middle provider.  Its only additional datum
is the exact carrier identity `z = ceil(D^(1/s))`; no cutoff error is added. -/
theorem sigmaEleven_add_sigmaTwelve_suzukiVProduct_le_finiteSourceLayer_add_qD_natCeil
    {S : BoundingSieve} {H : Section13HatLayers}
    {β C K d Δ s τ σ : ℝ} {N D z : ℕ}
    (hH : Section13HatContract H β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hD : 1 < (D : ℝ)) (hz2 : 2 ≤ (z : ℝ))
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hv2 : 2 ≤ (D : ℝ) ^ (1 / τ))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hwv : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / τ))
    (hvroot : (D : ℝ) ^ (1 / τ) ≤ (D : ℝ) ^ (1 / s))
    (hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hτerr : H.betaHat + (ErrorSign.ofDepth N).epsilon < τ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hCeil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / τ) → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / τ) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (h1413 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / τ) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    sigmaEleven (suzukiSupportedBelow S z) S.nu
        (fun p => suzukiVProduct S p) (suzukiVProduct S z)
        β N D σ τ +
      sigmaTwelve S.prodPrimes.primeFactors S.nu
        (fun p => suzukiVProduct S p)
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        (suzukiVProduct S z) C K Δ N D σ τ ≤
      suzukiVProduct S z *
        (finiteSourceLayer 1 β N s +
          (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
            Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
        (Real.log (D : ℝ)) ^ (-Δ) *
        ((1 / s) * (∫ t in τ..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
          (6 * K ^ 2 *
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ τ /
            Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) := by
  classical
  let w : ℝ := (D : ℝ) ^ (1 / σ)
  let v : ℝ := (D : ℝ) ^ (1 / τ)
  let r : ℝ := (D : ℝ) ^ (1 / s)
  have hVz : suzukiVProduct S (z : ℝ) = suzukiVProduct S r := by
    exact suzukiVProduct_natCeil_eq S (by simpa [r] using hzceil)
  have hPrime : ∀ F : ℝ → ℝ,
      suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v (z : ℝ) F =
        suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v r F := by
    intro F
    exact suzukiLemmaEightSevenPrimeSum_natCeil_eq S _ _ _ _ F
      (by simpa [r] using hzceil)
  have h11 := sigma11_middle_le_finiteSourceLayer_add_endpoint
    (S := S) (D := (D : ℝ)) (z := r) (v := v) (w := w)
    (s := s) (τ := τ) (σ := σ) (K := K) (β := β) (N := N)
    hH.beta_gt_one hsdom hτdom hsτ hτσ hD hroot2 hv2 hw2 hwv hvroot
    rfl rfl rfl hK hlocal
  have h11scaled := mul_le_mul_of_nonneg_left h11
    (suzukiVProduct_pos S r).le
  have h11final :
      sigmaEleven (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S p) (suzukiVProduct S z)
          β N D σ τ ≤
        suzukiVProduct S z *
          (finiteSourceLayer 1 β N s +
            (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
              Real.log w) * (τ / s)) := by
    have hrz : r ≤ (z : ℝ) :=
      (Nat.le_ceil r).trans_eq (congrArg Nat.cast hzceil).symm
    rw [sigmaEleven_eq_suzukiLemmaEightSevenPrimeSum S β σ τ w v N D z rfl rfl
      (hvroot.trans hrz)]
    rw [hPrime, hVz]
    exact h11scaled
  let Q : ℝ → ℝ := qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
  have hcarrier : sigmaOneCarrier S.prodPrimes.primeFactors D σ τ =
      S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v) := by
    ext p
    simp only [sigmaOneCarrier, Finset.mem_filter]
    rfl
  have hsum :
      (∑ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ τ,
        S.nu p * suzukiVProduct S (p : ℝ) / suzukiVProduct S (z : ℝ) *
          errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
            (inheritedCoordinate D p) *
          Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ^ (-Δ)) ≤
        (Real.log (D : ℝ)) ^ (-Δ) *
          suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v r Q := by
    rw [hcarrier]
    unfold suzukiLemmaEightSevenPrimeSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpz : (p : ℝ) < r := hp'.2.2.trans_le hvroot
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp'.1).2.1
    have hnu : 0 ≤ S.nu p := (S.nu_pos_of_prime p hpprime hpdiv).le
    have hsuffix : 0 ≤ ∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < r), (1 - S.nu q)⁻¹ := by
      apply Finset.prod_nonneg
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
      have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hq'.1).2.1
      exact inv_nonneg.mpr
        (sub_nonneg.mpr (S.nu_lt_one_of_prime q hqprime hqdiv).le)
    have herr := naturalCeil_inherited_error_le_claim14_13 H
      (hCeil p hp'.1 hp'.2.1 hp'.2.2).1
      (hCeil p hp'.1 hp'.2.1 hp'.2.2).2 hΔ
      (hT p hp'.1 hp'.2.1 hp'.2.2)
      (h1413 p hp'.1 hp'.2.1 hp'.2.2)
    rw [show S.nu p * suzukiVProduct S (p : ℝ) /
        suzukiVProduct S (z : ℝ) =
        S.nu p * (suzukiVProduct S (p : ℝ) /
          suzukiVProduct S (z : ℝ)) by ring]
    rw [hVz, suzukiVProduct_div_eq_suffix S hpz]
    dsimp [Q]
    have hmul := mul_le_mul_of_nonneg_left herr (mul_nonneg hnu hsuffix)
    nlinarith
  have houter : 0 ≤ C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) :=
    mul_nonneg (mul_nonneg hC (Real.exp_nonneg _)) (suzukiVProduct_pos S _).le
  have h12final :
      sigmaTwelve S.prodPrimes.primeFactors S.nu
          (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ N D σ τ ≤
        C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
          ((Real.log (D : ℝ)) ^ (-Δ) *
            ((1 / s) * (∫ t in τ..σ,
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
              (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
                  (D : ℝ) d Δ τ / Real.log w) * (τ / s))) := by
    unfold sigmaTwelve
    apply (mul_le_mul_of_nonneg_left hsum houter).trans
    apply mul_le_mul_of_nonneg_left _ houter
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.log_nonneg hD.le) _)
    exact sigma12_middle_le_qD_lemma8_7 (S := S) (H := H)
      (ErrorSign.ofDepth N) Q (fun p hp hpw hpv => le_rfl)
      hH hD hroot2 hv2 hw2 hwv hvroot rfl rfl rfl hτerr hτσ hK hlocal hii
  simpa only [w, mul_assoc] using add_le_add h11final h12final

/-- Rounded Case-II endpoint.  The source cutoff is the natural ceiling of the
real Case-II power coordinate; no perfect-power identity and no cutoff error
term is assumed. -/
theorem caseII_endpoint_le_concrete_finiteSourceLayer_add_qD_natCeil
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y : ℕ} {β σ C C1 K ΘK Δ d B0 : ℝ}
    (hH : Section13HatContract H β)
    (hN : Odd N) (hN2 : 2 ≤ N)
    (hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D)
    (hyceil : y = ⌈(D : ℝ) ^ (1 / (β + 1))⌉₊)
    (hyDhalf : (y : ℝ) ≤ (D : ℝ) / 2)
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
    (hClaim14_6_i : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ (β + 1),
      Claim14_6_MonotoneLambdaPremise H ((D ⌈/⌉ p : ℕ) : ℝ) d σ)
    (hErrorDomain : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ (β + 1),
      inheritedCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ ∧
      recursiveCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ)
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      β C K Δ N D σ (β + 1))
    (hErrorThreshold : H.betaHat + (ErrorSign.ofDepth N).epsilon < β + 1)
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
  have hτ : caseITau (D : ℝ) s = s := by
    exact caseITau_eq_beta_add_one_of_log_threshold hH.beta_gt_one hD hDlarge
  have hry : r ≤ (y : ℝ) := by
    exact (Nat.le_ceil r).trans_eq (congrArg Nat.cast hyceil).symm

  have hcaseI : Claim14_5CaseI β N s σ := by
    unfold Claim14_5CaseI
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    constructor
    · simp [s, hmod]
    · simpa [s] using hβ1σ
  have hsdom : s ∈ KappaOneModel.parityDomain β N := by
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    simp only [KappaOneModel.parityDomain, hmod, if_pos, Set.mem_Ioi]
    dsimp [s]
    linarith
  have hNm1mod : (N - 1) % 2 = 0 := by
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    omega
  have hsm1dom : s - 1 ∈ KappaOneModel.parityDomain β (N - 1) := by
    simp [KappaOneModel.parityDomain, hNm1mod, s]
  have hCeilSigma : ∀ p ∈ sigmaOneCarrier support D σ s,
      2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp
    have hp' := hp
    simp only [support, sigmaOneCarrier, suzukiSupportedBelow,
      Finset.mem_filter] at hp'
    apply hCeilFull p hp'.1.1 hp'.2.1
    have hpy : p < y := hp'.1.2
    simpa [r, s, hyceil, Nat.lt_ceil] using hpy
  have hSource : ∀ p ∈ sigmaOneCarrier support D σ s,
      finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p) := by
    intro p hp
    exact finiteSourceLayer_recursive_le_inherited hH.beta_gt_one (N - 1) D p
      (hCeilSigma p hp).1 (hCeilSigma p hp).2
      (hSourceDomain p (by simpa [support, s] using hp)).1
      (hSourceDomain p (by simpa [support, s] using hp)).2
  have hIHsource : PointwiseInductionContract support Tsrc
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      β C K Δ N D σ s :=
    naturalCeilContract_to_sourceCoordinate_errorEnvelope_of_claim14_6
      support Tsrc (fun p => suzukiVProduct S p) H β C K Δ d N D σ s hH
      (by
        intro p hp
        exact (suzukiVProduct_pos S (p : ℝ)).le)
      hC (by simpa [support, s] using hlog)
      hSource
      hCeilSigma
      (by simpa [support, s] using hClaim14_6_i)
      (by simpa [support, s] using hErrorDomain)
      (by simpa [support, Tsrc, s] using hIH)
  have h14 : sigmaOne support S.nu Tsrc N D σ s ≤
      sigmaEleven support S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S y) β N D σ s +
        sigmaTwelve support S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S y) C K Δ N D σ s :=
    equation14_10_finset_assembly support S.nu (fun p => suzukiVProduct S p)
      Tsrc (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S y) β C K Δ N D σ s
      (ne_of_gt (suzukiVProduct_pos S y))
      (by simpa [support, s] using hnu) hIHsource
  have hMiddleFull :=
    sigmaEleven_add_sigmaTwelve_suzukiVProduct_le_finiteSourceLayer_add_qD_natCeil
      (S := S) (H := H) (β := β) (C := C) (K := K) (d := d) (Δ := Δ)
      (s := s) (τ := s) (σ := σ) (N := N) (D := D) (z := y)
      hH hsdom hsm1dom le_rfl (by simpa [s] using hβ1σ) hD hy2
      (by simpa [s] using hroot2) (by simpa [s] using hroot2) hw2
      (by simpa [s] using hwy) le_rfl (by simpa [s] using hyceil)
      (by simpa [s] using hErrorThreshold) hK hlocal hClaim14_6_ii hC hΔ
      (by simpa [s] using hCeilFull) (by simpa [s] using hT)
      (by simpa [s] using hClaim14_13)
  have hCarrier := sigmaTwelve_supportedBelow_eq_full S
    (fun p => suzukiVProduct S p)
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S y) C K Δ N D y σ s hry
  have hMiddle :
      sigmaEleven support S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S y) β N D σ s +
        sigmaTwelve support S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S y) C K Δ N D σ s ≤
      suzukiVProduct S y *
        (finiteSourceLayer 1 β N s +
          (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (s - 1) /
            Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)) +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S y *
        (Real.log (D : ℝ)) ^ (-Δ) *
        ((1 / s) * (∫ t in s..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
          (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
              (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)) := by
    rw [show support = S.prodPrimes.primeFactors.filter (fun p => p < y) from rfl,
      hCarrier]
    exact hMiddleFull
  have hRec0 := suzukiSourceParitySum_recurrence_of_odd_of_supported_cube
    S hN hycube
  have hRec :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) =
        (∑ p ∈ (suzukiSupportedBelow S y).filter
            (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
          S.nu p * Tsrc (N - 1) (D ⌈/⌉ p) p) +
        (∑ p ∈ (suzukiSupportedBelow S y).filter
            (fun p : ℕ => (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧
              (p : ℝ) < (D : ℝ) ^ (1 / s)),
          S.nu p * Tsrc (N - 1) (D ⌈/⌉ p) p) := by
    rw [hRec0]
    rw [← Finset.sum_filter_add_sum_filter_not
      (suzukiSupportedBelow S y)
      (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ))]
    have hfilter :
        (suzukiSupportedBelow S y).filter
            (fun p : ℕ => ¬ (p : ℝ) < (D : ℝ) ^ (1 / σ)) =
          (suzukiSupportedBelow S y).filter
            (fun p : ℕ => (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧
              (p : ℝ) < (D : ℝ) ^ (1 / s)) := by
      ext p
      simp only [Finset.mem_filter, not_lt]
      constructor
      · rintro ⟨hp, hpw⟩
        refine ⟨hp, hpw, ?_⟩
        have hpy : p < y := (Finset.mem_filter.mp hp).2
        simpa [r, s, hyceil, Nat.lt_ceil] using hpy
      · rintro ⟨hp, hpw, _⟩
        exact ⟨hp, hpw⟩
    rw [hfilter]
  have hSigma0 :
      (∑ p ∈ (suzukiSupportedBelow S y).filter
          (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
        S.nu p * Tsrc (N - 1) (D ⌈/⌉ p) p) ≤ B0 := by
    have heq :
        (suzukiSupportedBelow S y).filter
            (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)) =
          suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊ := by
      rw [suzukiSupportedBelow_ceil_real]
      ext p
      simp only [suzukiSupportedBelow, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, _⟩, hpw⟩
        exact ⟨hp, hpw⟩
      · rintro ⟨hp, hpw⟩
        have hpyR : (p : ℝ) < r := hpw.trans_le (by simpa [r, s] using hwy)
        have hpy : p < y := by simpa [r, hyceil, Nat.lt_ceil] using hpyR
        exact ⟨⟨hp, hpy⟩, hpw⟩
    rw [heq]
    exact hEndpoint (claim14_5_sigma_endpoint_regime_of_caseI hcaseI)
  rw [hRec]
  apply add_le_add hSigma0
  change sigmaOne support S.nu Tsrc N D σ s ≤ _
  simpa [s] using h14.trans hMiddle


end MathlibNt.SieveTheory
