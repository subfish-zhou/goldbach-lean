import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146iErrorEnvelopeTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorEnvelopeTransportFull
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144RecursiveCoordinateSourceSigma
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

/-!
# Uniform Case-II quotient error transport

The Case-II carrier is the cubic strip, with upper endpoint `D^(1/3)` and
outer endpoint `sourceSigma D d`.  One cutoff, chosen before `D`, `N`, and the
Case-II coordinate `s`, puts every ceiling quotient above the internal
Claim-14.6 threshold.  The moving-coordinate theorem then puts the recursive
coordinate below the quotient's own source endpoint.
-/

/-- Carrierwise error transport required by the cubic Case-II pointwise
induction contract. -/
def CaseIIErrorEnvelopeTransport
    (S : BoundingSieve) (H : Section13HatLayers) (N D : ℕ) (d : ℝ) : Prop :=
  ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
      D (sourceSigma (D : ℝ) d) 3,
    errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
        (recursiveCoordinate D p) ≤
      errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
        (inheritedCoordinate D p)

theorem caseII_cubic_carrier_quotient_scale
    (S : BoundingSieve) {D Dmin : ℕ} {d : ℝ}
    (hDmin : 2 ≤ Dmin) (hD : Dmin ^ 2 ≤ D) :
    CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
      D Dmin (sourceSigma (D : ℝ) d) 3 := by
  intro p hp
  have hp' := hp
  simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
  have hpPrime : p.Prime := by
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp'.1).1
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (show 1 ≤ D by nlinarith)
  have hrootOrder : (D : ℝ) ^ (1 / (3 : ℝ)) ≤
      (D : ℝ) ^ (1 / (2 : ℝ)) :=
    rpow_one_div_mono_of_le hD1 (by norm_num) (by norm_num)
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) :=
    hp'.2.2.trans_le hrootOrder
  have hsquareR : (p : ℝ) ^ (2 : ℕ) < (D : ℝ) := by
    have hiff := Real.lt_rpow_inv_iff_of_pos
      (x := (p : ℝ)) (y := (D : ℝ)) (z := (2 : ℝ))
      (by positivity) (by positivity) (by norm_num)
    norm_num [one_div] at hiff hpRoot ⊢
    exact hiff.mp hpRoot
  have hsquare : p ^ 2 < D := by exact_mod_cast hsquareR
  by_cases hminp : Dmin ≤ p
  · calc
      Dmin * p ≤ p * p := Nat.mul_le_mul_right p hminp
      _ = p ^ 2 := by ring
      _ ≤ D := Nat.le_of_lt hsquare
  · have hpmin : p < Dmin := Nat.lt_of_not_ge hminp
    calc
      Dmin * p ≤ Dmin * Dmin := Nat.mul_le_mul_left Dmin (Nat.le_of_lt hpmin)
      _ = Dmin ^ 2 := by ring
      _ ≤ D := hD

/-- Uniform Case-II transport with the cutoff selected before the varying
bounding sieve.  The only local input is the parity-domain packet already
required by the rounded endpoint.  Coordinate ordering follows from natural
ceiling division; the recursive upper endpoint follows uniformly from the
moving quotient-source theorem; and Claim 14.6(i) is generated internally at
each quotient source endpoint.

The threshold is independent of `S`, `N`, and every `s ∈ (1,3]`. -/
theorem eventually_caseII_errorEnvelope_transport_uniform_in_S
    (H : Section13HatLayers) {d : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d) :
    ∀ᶠ D : ℕ in atTop, ∀ (S : BoundingSieve) (N : ℕ) (s : ℝ),
      Odd N → 1 < s → s ≤ 3 →
      (∀ p ∈ sigmaOneCarrier
          (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
          D (sourceSigma (D : ℝ) d) 3,
        inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) ∧
        recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
      CaseIIErrorEnvelopeTransport S H N D d := by
  obtain ⟨D146, hD146, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma
      (H := H) (d := d) (Δ := (1 / 2 : ℝ)) hH hd1 (by norm_num) (by norm_num)
  let C : ℝ := (1 + 3 * d) * (4 : ℝ) ^ d
  let A : ℝ := max D146 (Real.exp (3 * C))
  obtain ⟨Dmin, hDminA⟩ := exists_nat_gt A
  have hA1 : 1 < A := hD146.trans_le (le_max_left _ _)
  have hDmin2 : 2 ≤ Dmin := by
    have : (1 : ℝ) < (Dmin : ℝ) := hA1.trans hDminA
    exact_mod_cast this
  filter_upwards
    [eventually_ge_atTop (Dmin ^ 2),
      eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform hd1]
    with D hD hrecursiveUpper
  intro S N s _hN _hs1 _hs3 hdomains p hpCarrier
  have hpFull : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
      (sourceSigma (D : ℝ) d) 3 := by
    have hp := hpCarrier
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1.1, hp.2.1, hp.2.2⟩
  have hpSupport : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hpFull).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpSupport
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hp0 : 0 < p := hpPrime.pos
  have hscale := caseII_cubic_carrier_quotient_scale (d := d) S hDmin2 hD
  have hqThreshold : Dmin ≤ D ⌈/⌉ p :=
    ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
  have h2pD : 2 * p ≤ D :=
    (Nat.mul_le_mul_right p hDmin2).trans (hscale p hpCarrier)
  have hD146A : D146 ≤ A := le_max_left _ _
  have hD146min : D146 ≤ (Dmin : ℝ) :=
    hD146A.trans (le_of_lt hDminA)
  have hD146q : D146 ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
    exact hD146min.trans (by exact_mod_cast hqThreshold)
  have hi : Claim14_6_MonotoneLambdaPremise H
      ((D ⌈/⌉ p : ℕ) : ℝ) d
      (sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d) :=
    (h146 ((D ⌈/⌉ p : ℕ) : ℝ) hD146q).1
  have hq1 : 1 < ((D ⌈/⌉ p : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < D ⌈/⌉ p by omega)
  have hExpA : Real.exp (3 * C) ≤ A := le_max_right _ _
  have hExpq : Real.exp (3 * C) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) :=
    hExpA.trans ((le_of_lt hDminA).trans (by exact_mod_cast hqThreshold))
  have hlogLarge : 3 * C ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) :=
    (Real.le_log_iff_exp_le (by positivity)).2 hExpq
  have hlarge : (1 + 3 * d) * (4 : ℝ) ^ d ≤
      (1 / 3 : ℝ) * Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
    dsimp [C] at hlogLarge ⊢
    nlinarith
  exact errorEnvelope_coordinate_transport_full hH.toSection13HatContract
    (zero_le_one.trans hd1.le) hq1 hlarge hi
    (hdomains p hpCarrier).1 (coordinate_bounds hp2 h2pD).1
    (hrecursiveUpper S 3 (by norm_num) p hpFull)

/-- Compatibility wrapper for the original sieve-first Case-II transport API. -/
theorem eventually_caseII_errorEnvelope_transport_uniform
    (S : BoundingSieve) (H : Section13HatLayers) {d : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d) :
    ∀ᶠ D : ℕ in atTop, ∀ (N : ℕ) (s : ℝ), Odd N → 1 < s → s ≤ 3 →
      (∀ p ∈ sigmaOneCarrier
          (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
          D (sourceSigma (D : ℝ) d) 3,
        inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) ∧
        recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
      CaseIIErrorEnvelopeTransport S H N D d :=
  (eventually_caseII_errorEnvelope_transport_uniform_in_S H hH hd1).mono
    (fun _ hD => hD S)


end MathlibNt.SieveTheory
