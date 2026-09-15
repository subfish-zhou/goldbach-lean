import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorEnvelopeTransportFull
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

/-!
# Uniform Case-I carrier error transport

The Claim-14.6 source threshold is chosen before `D`, `N`, and `s`.  Enlarging
one natural global cutoff puts every ceiling quotient above that threshold and
also supplies the low-strip logarithmic estimate used by the full coordinate
transport theorem.
-/

/-- The carrierwise error-envelope comparison consumed by the Case-I
successor. -/
def CaseIErrorEnvelopeTransport
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D : ℕ) (d σ s : ℝ) : Prop :=
  ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ s,
    errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
      errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p)

/-- After one global quotient cutoff, full coordinate antitonicity gives the
Case-I error transport simultaneously at every carrier.  The two coordinate
hypotheses are exactly the geometric facts supplied by the Case-I pointwise
packet: the inherited point is in the predecessor parity domain and the
recursive point is below the quotient's source endpoint. -/
theorem exists_caseI_errorEnvelope_transport_quotient_cutoff_uniform_in_S
    (H : Section13HatLayers) {d Δ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ (S : BoundingSieve) (D N : ℕ) (s : ℝ),
        CarrierQuotientThresholdGeometry S.prodPrimes.primeFactors D Dmin
          (sourceSigma (D : ℝ) d) s →
        (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
            (sourceSigma (D : ℝ) d) s,
          inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
        (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
            (sourceSigma (D : ℝ) d) s,
          recursiveCoordinate D p ≤
            sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d) →
        CaseIErrorEnvelopeTransport S H N D d (sourceSigma (D : ℝ) d) s := by
  obtain ⟨D146, hD146, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma
      hH hd1 hΔ0 hΔ1
  let C : ℝ := (1 + 3 * d) * (4 : ℝ) ^ d
  let A : ℝ := max D146 (Real.exp (3 * C))
  obtain ⟨Dmin, hDminA⟩ := exists_nat_gt A
  have hA1 : 1 < A := hD146.trans_le (le_max_left _ _)
  have hDmin2 : 2 ≤ Dmin := by
    have : (1 : ℝ) < (Dmin : ℝ) := hA1.trans hDminA
    exact_mod_cast this
  refine ⟨Dmin, hDmin2, ?_⟩
  intro S D N s hscale hinherited hrecursiveUpper p hpCarrier
  have hpSupport : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hpCarrier).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpSupport
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hp0 : 0 < p := hpPrime.pos
  have hqThreshold : Dmin ≤ D ⌈/⌉ p :=
    ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
  have hq2 : 2 ≤ D ⌈/⌉ p := hDmin2.trans hqThreshold
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
  have hq1 : 1 < ((D ⌈/⌉ p : ℕ) : ℝ) := by exact_mod_cast (show 1 < D ⌈/⌉ p by omega)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by nlinarith) (Real.rpow_nonneg (by norm_num) _)
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
    (hinherited p hpCarrier) (coordinate_bounds hp2 h2pD).1
    (hrecursiveUpper p hpCarrier)

/-- Compatibility specialization of the sieve-uniform quotient cutoff. -/
theorem exists_caseI_errorEnvelope_transport_quotient_cutoff
    (S : BoundingSieve) (H : Section13HatLayers) {d Δ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ (D N : ℕ) (s : ℝ),
        CarrierQuotientThresholdGeometry S.prodPrimes.primeFactors D Dmin
          (sourceSigma (D : ℝ) d) s →
        (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
            (sourceSigma (D : ℝ) d) s,
          inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
        (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
            (sourceSigma (D : ℝ) d) s,
          recursiveCoordinate D p ≤
            sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d) →
        CaseIErrorEnvelopeTransport S H N D d (sourceSigma (D : ℝ) d) s := by
  obtain ⟨Dmin, hDmin, hall⟩ :=
    exists_caseI_errorEnvelope_transport_quotient_cutoff_uniform_in_S
      H hH hd1 hΔ0 hΔ1
  exact ⟨Dmin, hDmin, fun D N s => hall S D N s⟩


/-- A square global cutoff puts every Case-I carrier quotient above the threshold. -/
theorem caseI_carrier_quotient_scale
    (S : BoundingSieve) {D Dmin : ℕ} {σ s : ℝ}
    (hDmin : 2 ≤ Dmin) (hD : Dmin ^ 2 ≤ D) (hs : 2 ≤ s) :
    CarrierQuotientThresholdGeometry S.prodPrimes.primeFactors D Dmin σ s := by
  intro p hp
  have hp' := hp
  simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (show 1 ≤ D by nlinarith)
  have hrootOrder : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 / (2 : ℝ)) :=
    rpow_one_div_mono_of_le hD1 (by norm_num) hs
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

/-- Eventual form: the square global cutoff and `p < D^(1/s)`, `s ≥ 2`
put every natural ceiling quotient above the internal Claim-14.6 threshold.
The cutoff precedes `N` and `s`. -/
theorem eventually_caseI_errorEnvelope_transport_uniform_in_S
    (H : Section13HatLayers) {d Δ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∀ᶠ D : ℕ in atTop, ∀ (S : BoundingSieve) (N : ℕ) (s : ℝ), 2 ≤ s →
      (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
          (sourceSigma (D : ℝ) d) s,
        inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
      (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
          (sourceSigma (D : ℝ) d) s,
        recursiveCoordinate D p ≤
          sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d) →
      CaseIErrorEnvelopeTransport S H N D d (sourceSigma (D : ℝ) d) s := by
  obtain ⟨Dmin, hDmin, htransport⟩ :=
    exists_caseI_errorEnvelope_transport_quotient_cutoff_uniform_in_S
      H hH hd1 hΔ0 hΔ1
  filter_upwards [eventually_ge_atTop (Dmin ^ 2)] with D hD
  intro S N s hs hinherited hrecursiveUpper
  exact htransport S D N s
    (caseI_carrier_quotient_scale S hDmin hD hs)
    hinherited hrecursiveUpper

/-- Compatibility specialization of the sieve-uniform eventual theorem. -/
theorem eventually_caseI_errorEnvelope_transport_uniform
    (S : BoundingSieve) (H : Section13HatLayers) {d Δ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∀ᶠ D : ℕ in atTop, ∀ (N : ℕ) (s : ℝ), 2 ≤ s →
      (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
          (sourceSigma (D : ℝ) d) s,
        inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
      (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
          (sourceSigma (D : ℝ) d) s,
        recursiveCoordinate D p ≤
          sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d) →
      CaseIErrorEnvelopeTransport S H N D d (sourceSigma (D : ℝ) d) s :=
  (eventually_caseI_errorEnvelope_transport_uniform_in_S H hH hd1 hΔ0 hΔ1).mono
    (fun _ hD => hD S)


end MathlibNt.SieveTheory
