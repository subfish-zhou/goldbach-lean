import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0Exact
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma11Internal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SigmaTwoZeroKappaOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0EndpointTransport

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure

set_option maxHeartbeats 2000000

/-!
# Lemma 14.4, Case I: unconditional same-constant successor

This is the final assembly against the source interfaces.  The recurrence and
IH are the actual finite ones; `Σ₀` is first identified with the single source
endpoint, `Σ₁₁` is the internal Lemma-8.7 estimate, `Σ₁₂` uses the natural
ceiling, and `Σ₂` vanishes in the genuine `κ = 1` Case-I range.

The only upstream name intentionally isolated by this file is
`caseI1423_sigmaZero_realEndpoint_sourceBound`.  It is the expected real
endpoint source estimate for the *explicit Claim-14.5 remainder*, not a bound
on `Σ₀`, a `mainSum` estimate, or an absorption hypothesis.  Once that producer
is present, the theorem below has no `Sigma`-bound, `mainSum`, or absorption
premise.
-/

/-- Eventual Case-I successor with literally the same constant `C` in the
induction hypothesis, inherited budget, and conclusion. -/
theorem lemma14_4_caseI_successor_sameC_eventually
    (S : BoundingSieve) (H : Section13HatLayers)
    {N Dmin : ℕ} {C C145 K d Δ s : ℝ}
    (hN : 2 ≤ N)
    (hsdom : s ∈ KappaOneModel.parityDomain 2 N)
    (hspred : s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1))
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hs : 2 ≤ s)
    (hsLower : 2 + (ErrorSign.ofDepth N).epsilon ≤ s)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hC : 0 < C) (hC145 : 0 < C145)
    (hDmin : 2 ≤ Dmin) :
    ∀ᶠ D : ℕ in atTop,
      let σ := sourceSigma (D : ℝ) d
      let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
      4 ≤ D →
      1 < σ → s ≤ σ →
      2 ≤ (D : ℝ) ^ (1 / s) →
      2 ≤ (D : ℝ) ^ (1 / σ) →
      (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / s) →
      H.betaHat + (ErrorSign.ofDepth N).epsilon < s →
      (Odd N → z ^ 3 ≤ D) →
      (∀ p ∈ suzukiSupportedBelow S z, p.Prime) →
      CarrierQuotientThresholdGeometry
        (suzukiSupportedBelow S z) D Dmin σ s →
      (∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
        inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
      (∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
        finiteSourceLayer 1 2 (N - 1) (recursiveCoordinate D p) ≤
          finiteSourceLayer 1 2 (N - 1) (inheritedCoordinate D p)) →
      (∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
        errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
          errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d
            (inheritedCoordinate D p)) →
      GlobalDepthLemma144InductionHypothesis
        (suzukiActualT S) (fun p => suzukiVProduct S p)
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        2 C K Δ (N - 1) Dmin →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p)) →
      suzukiActualT S N D z ≤
        suzukiVProduct S z * finiteSourceLayer 1 2 N s +
          sigma12InheritedBudget S H N D z C K d Δ s := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  obtain ⟨D12, hD12, h12⟩ := eventually_sigmaTwelve_internal_contraction_sameC
    (S := S) (H := H) (C := C) (K := K) (d := d) (Δ := Δ)
    (s := s) (N := N) hH hN hd1 hΔ0 hΔ1 hs0
    hsLower hK hlocal hC.le
  obtain ⟨D0, hD0, hzero⟩ := suzukiSigmaZero_sourceSigma_eventually
    S H hΔ0 hΔ1 hd (lt_of_lt_of_le (by norm_num) hK) hC145 hlocal hH
  obtain ⟨A0, hA0, hzeroSource⟩ :=
    caseI1423_sigmaZero_realEndpoint_sourceBound
      S H C C145 K d Δ hH hd1 hΔ0 hΔ1 hC hC145.le
  obtain ⟨A11, A12, hA11, hA12, hendpoint⟩ :=
    caseI1423EndpointSourceBoundsFinal S H C K d Δ hH hC hΔ0 hΔ1 hd
  have hcoefR := eventually_caseISourceOrderCoefficient_le_sameC_gap
    (A := A0 + A11 + A12) (by positivity) hΔ0 hΔ1 hd
  have hcoefN := tendsto_natCast_atTop_atTop.eventually hcoefR
  have hD12N : ∀ᶠ D : ℕ in atTop, D12 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D12)
  have hD0N : ∀ᶠ D : ℕ in atTop, D0 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D0)
  filter_upwards
      [hzeroSource N s hsLower, hendpoint N s hN hs hspred, hcoefN, hD12N, hD0N]
    with D hzeroSrc hend hcoefD hlarge12 hlarge0
  dsimp only at hzeroSrc hend hcoefD ⊢
  intro hD4 hσ1 hsσ hv2 hw2 hwv hthreshold hOdd hprime hscale
    hinherited hSource hError hglobal hCeil hT
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊ := rfl
  have hzσ : (D : ℝ) ^ (1 / σ) ≤ (z : ℝ) := by
    change (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤
      (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)
    exact hwv.trans (Nat.le_ceil _)
  have hOddσ : Odd N → ⌈(D : ℝ) ^ (1 / σ)⌉₊ ^ 3 ≤ D := by
    intro hodd
    have hceil : ⌈(D : ℝ) ^ (1 / σ)⌉₊ ≤ z := by
      change ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ ≤
        ⌈(D : ℝ) ^ (1 / s)⌉₊
      exact Nat.ceil_le.mpr (hwv.trans (Nat.le_ceil _))
    exact (Nat.pow_le_pow_left hceil 3).trans (hOdd hodd)
  have hzeroRaw := hzero D N z hlarge0 hN hzσ hOddσ
  have hzeroDirect : suzukiSigmaZero S N D z ((D : ℝ) ^ (1 / σ)) ≤
      caseISigmaZeroDirectRemainder S H N D C145 K d Δ := by
    simpa [σ, caseISigmaZeroDirectRemainder] using hzeroRaw
  have hpoint : PointwiseInductionContract
      (suzukiSupportedBelow S z) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ s :=
    pointwiseInductionContract_of_globalDepthIH
      (suzukiSupportedBelow S z) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D Dmin σ s hDmin hprime hscale hinherited
      (by intro p hp; exact (suzukiVProduct_pos S p).le) hC.le hSource hError hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (suzukiActualT S) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ N D σ s
    (ne_of_gt (suzukiVProduct_pos S z))
    (by
      intro p hp
      have hpS := (Finset.mem_filter.mp hp).1
      exact (S.nu_pos_of_prime p (hprime p hpS)
        ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le)
    hpoint
  have h149 := suzuki_equation14_9 S hN hOdd
    (a := (D : ℝ) ^ (1 / σ)) (b := (D : ℝ) ^ (1 / s)) hwv
  have h11raw := caseI_sigmaEleven_le_finiteSourceLayer_add_endpoint
    (S := S) (β := (2 : ℝ)) (s := s) (τ := s) (σ := σ)
    (K := K) (N := N) (D := D) (z := z)
    (by norm_num) hsdom hspred le_rfl hsσ hDreal hv2 hv2 hw2 hwv le_rfl hz hK hlocal
  have h11 : sigmaEleven (suzukiSupportedBelow S z) S.nu
      (fun p => suzukiVProduct S p) (suzukiVProduct S z) 2 N D σ s ≤
      suzukiVProduct S z * finiteSourceLayer 1 2 N s +
        caseI1423Sigma11Endpoint S N D z K s σ := by
    simpa [caseI1423Sigma11Endpoint, div_self (ne_of_gt hs0)] using h11raw
  obtain ⟨q12, hq12, _h12raw, h12q⟩ :=
    h12 D z hlarge12 hσ1 hsσ hDreal hv2 hw2 hwv hz hthreshold hCeil hT
  have hcarrier :
      sigmaOneCarrier (suzukiSupportedBelow S z) D σ s =
        sigmaOneCarrier S.prodPrimes.primeFactors D σ s := by
    ext p
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpS, _⟩, hpw, hpv⟩; exact ⟨hpS, hpw, hpv⟩
    · rintro ⟨hpS, hpw, hpv⟩
      exact ⟨⟨hpS, (nat_lt_natCeil_iff_lt_real
        (natCast_rpow_one_div_pos (by omega) s) hz).2 hpv⟩, hpw, hpv⟩
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ N D σ s ≤
        q12.ρ * sigma12InheritedBudget S H N D z C K d Δ s +
          caseI1423Sigma12Endpoint S H N D z C K d Δ s σ := by
    unfold sigmaTwelve at h12q ⊢
    rw [hcarrier]
    simpa [σ, caseI1423Sigma12Endpoint, sigma12EndpointRemainder,
      div_self (ne_of_gt hs0)] using h12q
  obtain ⟨qgap, hqgap, hcoef⟩ := hcoefD
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H N D z C K d Δ s := by
    unfold sigma12InheritedBudget
    have hE : 0 ≤ errorEnvelope H N (D : ℝ) d s :=
      errorEnvelope_nonneg H N hDreal hs0.le
        (hH.positive (ErrorSign.ofDepth N) s hs0).le
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hC.le (Real.exp_pos _).le)
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ D)) (-Δ)))
      hE
  have hunit : (A0 + A11 + A12) *
        caseI1423RemainderUnit
          (sigma12InheritedBudget S H N D z C K d Δ s) (D : ℝ) σ =
      caseISourceOrderCoefficient (A0 + A11 + A12) (D : ℝ) d *
        sigma12InheritedBudget S H N D z C K d Δ s := by
    simp [caseI1423RemainderUnit, caseISourceOrderCoefficient, σ]
    ring
  have hside :
      caseISigmaZeroDirectRemainder S H N D C145 K d Δ +
          caseI1423Sigma11Endpoint S N D z K s σ +
          caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
        (1 - q12.ρ) * sigma12InheritedBudget S H N D z C K d Δ s := by
    have hzeroSrc' := hzeroSrc hsσ
    have hend' := hend hsσ
    have hsrc :
        caseISigmaZeroDirectRemainder S H N D C145 K d Δ +
            caseI1423Sigma11Endpoint S N D z K s σ +
            caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
          (A0 + A11 + A12) * caseI1423RemainderUnit
            (sigma12InheritedBudget S H N D z C K d Δ s) (D : ℝ) σ := by
      linarith [hzeroSrc', hend'.1, hend'.2]
    calc
      _ ≤ caseISourceOrderCoefficient (A0 + A11 + A12) (D : ℝ) d *
          sigma12InheritedBudget S H N D z C K d Δ s := by simpa [hunit] using hsrc
      _ ≤ (1 - qgap.ρ) * sigma12InheritedBudget S H N D z C K d Δ s :=
        mul_le_mul_of_nonneg_right hcoef hbudget
      _ = _ := by rw [hqrho]
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := N) S hD4 hs hz
  have htau : lemma144RealTau D s = s := lemma144_realTau_eq_s_of_caseI hD4 hs
  have h2 : suzukiSigmaTwo S N D z ((D : ℝ) ^ (1 / s)) = 0 := by
    simpa [htau] using h2raw
  have hmiddle : suzukiSigmaOne S N D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / s)) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S p) (suzukiVProduct S z) 2 N D σ s +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ N D σ s := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S)
      N D σ s ≤ _
    exact h10
  rw [h149, h2]
  linarith [hzeroDirect, hmiddle, h11, h12qSupported, hside]


end MathlibNt.SieveTheory
