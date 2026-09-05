import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0EndpointTransportUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeilUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISuccessorFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0ExactStrictCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure

set_option maxHeartbeats 2000000

/-!
# Lemma 14.4, Case I: uniform-in-`s` same-constant successor

This is the final assembly against the source interfaces.  The recurrence and
IH are the actual finite ones; `Σ₀` is first identified with the single source
endpoint, `Σ₁₁` is the internal Lemma-8.7 estimate, `Σ₁₂` uses the natural
ceiling, and `Σ₂` vanishes in the genuine `κ = 1` Case-I range.

The real endpoint, `Σ₀` transport, and `Σ₁₂` contraction estimates are
consumed through their production uniform source interfaces, not as bounds on a
`Sigma` term, a `mainSum` estimate, or an absorption hypothesis.
-/

/-- Uniform Case-I successor with literally the same `C`: one cutoff precedes
`N,s`, and every geometry/IH premise follows those binders. -/
theorem lemma14_4_caseI_successor_sameC_uniform_strict
    (S : BoundingSieve) (H : Section13HatLayers)
    {Dmin : ℕ} {C C145 K d Δ : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hC : 0 < C) (hC145 : 0 < C145)
    (hDmin : 2 ≤ Dmin) :
    ∀ᶠ D : ℕ in atTop, ∀ (N : ℕ) (s : ℝ),
      2 ≤ N →
      s ∈ KappaOneModel.parityDomain 2 N →
      s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) →
      2 ≤ s →
      2 + (ErrorSign.ofDepth N).epsilon ≤ s →
      let σ := sourceSigma (D : ℝ) d
      let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
      4 ≤ D →
      1 < σ → s ≤ σ →
      2 ≤ (D : ℝ) ^ (1 / s) →
      2 ≤ (D : ℝ) ^ (1 / σ) →
      (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / s) →
      H.betaHat + (ErrorSign.ofDepth N).epsilon < s →
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
  obtain ⟨D0, _hD0, hzero⟩ := suzukiSigmaZero_sourceSigma_eventually_strict
    S H hΔ0 hΔ1 hd (lt_of_lt_of_le (by norm_num) hK) hC145 hlocal hH
  obtain ⟨A0, hA0, hzeroSource⟩ :=
    caseI1423_sigmaZero_realEndpoint_sourceBound_uniform
      S H C C145 K d Δ hH hd1 hΔ0 hΔ1 hC hC145.le
  obtain ⟨A11, A12, hA11, hA12, hendpoint⟩ :=
    caseI1423EndpointSourceBoundsUniform S H C K d Δ hH hC hΔ0 hΔ1 hd
  obtain ⟨D12, _hD12, h12⟩ :=
    eventually_sigmaTwelve_internal_contraction_sameC_uniform
      (S := S) (H := H) (C := C) (K := K) (d := d) (Δ := Δ)
      hH hd1 hΔ0 hΔ1 hK hlocal hC.le
  have hcoefR := eventually_caseISourceOrderCoefficient_le_sameC_gap
    (A := A0 + A11 + A12) (by positivity) hΔ0 hΔ1 hd
  have hcoefN := tendsto_natCast_atTop_atTop.eventually hcoefR
  have hD12N : ∀ᶠ D : ℕ in atTop, D12 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D12)
  have hD0N : ∀ᶠ D : ℕ in atTop, D0 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D0)
  filter_upwards [hD12N, hzeroSource, hendpoint, hcoefN, hD0N]
    with D hlarge12 hzeroSrcD hendD hcoefD hlarge0
  intro N s hN hsdom hspred hs hsLower
  dsimp only
  intro hD4 hσ1 hsσ hv2 hw2 hwv hthreshold hprime hscale
    hinherited hSource hError hglobal hCeil hT
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hzeroSrc := hzeroSrcD N s hsLower hsσ
  have hend := hendD N s hN hs hspred hsσ
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊ := rfl
  have hzσ : (D : ℝ) ^ (1 / σ) ≤ (z : ℝ) := by
    change (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤
      (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)
    exact hwv.trans (Nat.le_ceil _)
  have hzeroRaw := hzero D N z hlarge0 hN hzσ
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
  have h149 : suzukiActualT S N D z =
      suzukiSigmaZero S N D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S N D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / s)) +
          suzukiSigmaTwo S N D z ((D : ℝ) ^ (1 / s)) := by
    by_cases hOddN : Odd N
    · have hs3 : 3 ≤ s := by
        norm_num [ErrorSign.ofDepth, hOddN, ErrorSign.epsilon] at hsLower
        exact hsLower
      exact suzuki_equation14_9_natCeil S hN (by omega) hs3 hz hwv
    · exact suzuki_equation14_9_strict S hN
        (by intro hodd; exact (hOddN hodd).elim) hwv
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
    h12 D hlarge12 N s z hN hs0 hsLower hσ1 hsσ hDreal hv2 hw2 hwv hz
      hthreshold.le hCeil hT
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
    simpa [caseI1423Sigma12Endpoint, sigma12EndpointRemainder,
      div_self (ne_of_gt hs0)] using h12q
  obtain ⟨qgap, hqgap, hcoef⟩ := hcoefD
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H N D z C K d Δ s := by
    unfold sigma12InheritedBudget
    have hE : 0 ≤ errorEnvelope H N (D : ℝ) d s := by
      apply errorEnvelope_nonneg H N hDreal hs0.le
      exact (hH.positive (ErrorSign.ofDepth N) s hs0).le
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hC.le (Real.exp_nonneg _)) (suzukiVProduct_pos S z).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _)) hE
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
    have hsrc :
        caseISigmaZeroDirectRemainder S H N D C145 K d Δ +
            caseI1423Sigma11Endpoint S N D z K s σ +
            caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
          (A0 + A11 + A12) * caseI1423RemainderUnit
            (sigma12InheritedBudget S H N D z C K d Δ s) (D : ℝ) σ := by
      linarith [hzeroSrc, hend.1, hend.2]
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
