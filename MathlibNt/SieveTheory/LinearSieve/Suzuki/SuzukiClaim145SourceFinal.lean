import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseABoundedK
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseALowSFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAHighSFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceBranchInterface
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIEndpointRegime

open scoped Classical BigOperators

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-!
# Claim 14.5: closed source assembly boundary

This module first combines the three genuine Case-A producers.  It then records
an end-to-end source theorem whose Case-B argument is the exact uniform-in-`C1`
closed producer required by the paper.  In particular, the eventual-in-`D`
`claim145_sourceSigma_allS_internal` theorem is not silently promoted to this
stronger quantifier order.
-/

/-- The three production Case-A leaves give one threshold and one positive
constant.  The bounded range is closed only after the two large-`K` thresholds
have been fixed, so its finite-range constant has the correct dependence. -/
theorem exists_claim145_caseA_closed
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hd2 : 2 < d) (hC1 : 0 < C1) (hΘ : 0 < Θ)
    (hsource : 2 / d < 1 / Θ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hgap : 0 < d - 2 * Θ) :
    ∃ K0 CA : ℝ, 2 ≤ K0 ∧ 0 < CA ∧
      Claim145CaseABoundedKClosed S H d Δ C1 Θ K0 CA ∧
      Claim145CaseALargeKLowSClosed S H d Δ C1 Θ K0 CA ∧
      Claim145CaseALargeKHighSClosed S H d Δ C1 Θ K0 CA := by
  obtain ⟨Klow, hKlow, hlow⟩ := claim145_caseA_lowS_actual S H hH
    hC1.le hΘ (by linarith) hsource hΔ0.le hΔ1.le
  obtain ⟨Khigh, hKhigh, hhigh⟩ := claim145_caseA_highS_actual S H hH
    hC1 hΘ.le hΔ0.le hΔ1.le hgap
  let K0 : ℝ := max Klow Khigh
  have hK0 : 2 ≤ K0 := hKlow.trans (le_max_left _ _)
  obtain ⟨Cbounded, hCbounded, hbounded⟩ :=
    exists_claim14_5Bound_caseA_boundedK S H hH hd2 hC1.le hΘ.le
      (show 1 ≤ K0 by linarith)
  let CA : ℝ := max Cbounded 1
  have hCA : 0 < CA := hCbounded.trans_le (le_max_left _ _)
  refine ⟨K0, CA, hK0, hCA, ?_, ?_, ?_⟩
  · intro K N D s hK hKK hlocal hD hs hsmall
    have hb := hbounded N D ⌈(D : ℝ) ^ (1 / s)⌉₊ K s
      (by linarith) hKK hlocal hD rfl hs hsmall
    have hb' : ActualClaim145BoundAt S H N D d Δ K s Cbounded := by
      simpa only [ActualClaim145BoundAt, Claim14_5Bound, Nat.ceil_natCast] using hb
    exact hb'.mono_constant S H hH hD hs (le_max_left _ _)
  · intro K N D s hKK hlocal hD hs hsupper hsmall
    have hKlowK : Klow ≤ K := (le_max_left Klow Khigh).trans hKK
    exact (hlow K N D s hKlowK hlocal hD hs hsupper hsmall).mono_constant
      S H hH hD hs (le_max_right _ _)
  · intro K N D s hKK hlocal hD hs hslower hsmall
    have hKhighK : Khigh ≤ K := (le_max_right Klow Khigh).trans hKK
    exact (hhigh K N D s hKhighK hlocal hD hs hslower hsmall).mono_constant
      S H hH hD hs (le_max_right _ _)

/-- The three Case-A branches with thresholds and coefficient selected before
any bounding sieve. -/
theorem exists_claim145_caseA_closed_uniform_in_S
    (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hd2 : 2 < d) (hC1 : 0 < C1) (hΘ : 0 < Θ)
    (hsource : 2 / d < 1 / Θ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hgap : 0 < d - 2 * Θ) :
    ∃ K0 CA : ℝ, 2 ≤ K0 ∧ 0 < CA ∧
      ∀ S : BoundingSieve,
        Claim145CaseABoundedKClosed S H d Δ C1 Θ K0 CA ∧
        Claim145CaseALargeKLowSClosed S H d Δ C1 Θ K0 CA ∧
        Claim145CaseALargeKHighSClosed S H d Δ C1 Θ K0 CA := by
  obtain ⟨Klow, hKlow, hlow⟩ := claim145_caseA_lowS_actual_uniform_in_S H hH
    hC1.le hΘ (by linarith) hsource hΔ0.le hΔ1.le
  obtain ⟨Khigh, hKhigh, hhigh⟩ := claim145_caseA_highS_actual_uniform_in_S H hH
    hC1 hΘ.le hΔ0.le hΔ1.le hgap
  let K0 : ℝ := max Klow Khigh
  have hK0 : 2 ≤ K0 := hKlow.trans (le_max_left _ _)
  obtain ⟨Cbounded, hCbounded, hbounded⟩ :=
    exists_claim14_5Bound_caseA_boundedK_uniform_in_S H hH hd2 hC1.le hΘ.le
      (show 1 ≤ K0 by linarith)
  let CA : ℝ := max Cbounded 1
  have hCA : 0 < CA := hCbounded.trans_le (le_max_left _ _)
  refine ⟨K0, CA, hK0, hCA, ?_⟩
  intro S
  refine ⟨?_, ?_, ?_⟩
  · intro K N D s hK hKK hlocal hD hs hsmall
    have hb := hbounded S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ K s
      (by linarith) hKK hlocal hD rfl hs hsmall
    have hb' : ActualClaim145BoundAt S H N D d Δ K s Cbounded := by
      simpa only [ActualClaim145BoundAt, Claim14_5Bound, Nat.ceil_natCast] using hb
    exact hb'.mono_constant S H hH hD hs (le_max_left _ _)
  · intro K N D s hKK hlocal hD hs hsupper hsmall
    have hKlowK : Klow ≤ K := (le_max_left Klow Khigh).trans hKK
    exact (hlow S K N D s hKlowK hlocal hD hs hsupper hsmall).mono_constant
      S H hH hD hs (le_max_right _ _)
  · intro K N D s hKK hlocal hD hs hslower hsmall
    have hKhighK : Khigh ≤ K := (le_max_right Klow Khigh).trans hKK
    exact (hhigh S K N D s hKhighK hlocal hD hs hslower hsmall).mono_constant
      S H hH hD hs (le_max_right _ _)

/-- Complete source Claim 14.5 uniformly in the varying bounding sieve. -/
theorem claim145_source_actual_of_uniform_caseB_uniform_in_S
    (H : Section13HatLayers)
    {d Δ C1 Θ C1min CB : ℝ}
    (hH : Section13HatSourceContract H)
    (hd2 : 2 < d) (hC1pos : 0 < C1) (hΘ : 0 < Θ)
    (hsource : 2 / d < 1 / Θ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hgap : 0 < d - 2 * Θ)
    (hC1 : C1min ≤ C1)
    (hB : ∀ S : BoundingSieve, Claim145CaseBClosed S H d Δ Θ C1min CB) :
    ∃ C145 : ℝ, 0 < C145 ∧
      ∀ (S : BoundingSieve) (K : ℝ) (N D : ℕ) (s : ℝ),
        2 ≤ K → HasDimensionOneLocalProductBound S K →
        2 ≤ D → 2 ≤ s →
        (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨
          sourceSigma (D : ℝ) d ≤ s) →
        ActualClaim145BoundAt S H N D d Δ K s C145 := by
  obtain ⟨K0, CA, _hK0, hCA, hallA⟩ :=
    exists_claim145_caseA_closed_uniform_in_S H hH hd2 hC1pos hΘ hsource
      hΔ0 hΔ1 hgap
  refine ⟨max CA CB, hCA.trans_le (le_max_left _ _), ?_⟩
  intro S K N D s hK hlocal hD hs hregime
  rcases hallA S with ⟨hbounded, hlow, hhigh⟩
  exact claim145_actual_of_closed_source_branches S H hH hC1 hK hlocal hD hs
    hbounded hlow hhigh (hB S) hregime

/-- Complete source Claim 14.5 after supplying a genuine Case-B producer with
`CB` and `C1min` chosen before the varying `C1`.  The source disjunction is kept
literal.  Crucially, the final constant is chosen before `K,N,D,s`. -/
theorem claim145_source_actual_of_uniform_caseB
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ C1min CB : ℝ}
    (hH : Section13HatSourceContract H)
    (hd2 : 2 < d) (hC1pos : 0 < C1) (hΘ : 0 < Θ)
    (hsource : 2 / d < 1 / Θ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hgap : 0 < d - 2 * Θ)
    (hC1 : C1min ≤ C1)
    (hB : Claim145CaseBClosed S H d Δ Θ C1min CB) :
    ∃ C145 : ℝ, 0 < C145 ∧
      ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
        2 ≤ K → HasDimensionOneLocalProductBound S K →
        2 ≤ D → 2 ≤ s →
        (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨
          sourceSigma (D : ℝ) d ≤ s) →
        ActualClaim145BoundAt S H N D d Δ K s C145 := by
  obtain ⟨K0, CA, _hK0, hCA, hbounded, hlow, hhigh⟩ :=
    exists_claim145_caseA_closed S H hH hd2 hC1pos hΘ hsource hΔ0 hΔ1 hgap
  refine ⟨max CA CB, hCA.trans_le (le_max_left _ _), ?_⟩
  intro K N D s hK hlocal hD hs hregime
  exact claim145_actual_of_closed_source_branches S H hH hC1 hK hlocal hD hs
    hbounded hlow hhigh hB hregime

/-- Public `Claim14_5Bound` spelling of the complete source result, retaining the
same constant-before-variables quantifier order. -/
theorem claim145_source_claim14_5Bound_of_uniform_caseB
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ C1min CB : ℝ}
    (hH : Section13HatSourceContract H)
    (hd2 : 2 < d) (hC1pos : 0 < C1) (hΘ : 0 < Θ)
    (hsource : 2 / d < 1 / Θ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hgap : 0 < d - 2 * Θ)
    (hC1 : C1min ≤ C1)
    (hB : Claim145CaseBClosed S H d Δ Θ C1min CB) :
    ∃ C145 : ℝ, 0 < C145 ∧
      ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
        2 ≤ K → HasDimensionOneLocalProductBound S K →
        2 ≤ D → 2 ≤ s →
        (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨
          sourceSigma (D : ℝ) d ≤ s) →
        Claim14_5Bound
          (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
          S H N (D : ℝ) (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s C145 := by
  obtain ⟨C145, hC145, hclosed⟩ := claim145_source_actual_of_uniform_caseB
    S H hH hd2 hC1pos hΘ hsource hΔ0 hΔ1 hgap hC1 hB
  refine ⟨C145, hC145, ?_⟩
  intro K N D s hK hlocal hD hs hregime
  have h := hclosed K N D s hK hlocal hD hs hregime
  simpa only [ActualClaim145BoundAt, Claim14_5Bound, Nat.ceil_natCast] using h

/-- Direct Claim-14.5 endpoint provider for the `hEndpoint` argument of
`caseI_total_le_sigma0_add_sigma11_add_sigma12`.  This is the source induction
interface: the exact recurrence identifies the endpoint prime sum with
`suzukiActualT`; no `Dmin` or hybrid finite-quotient split is introduced. -/
theorem claim145_actual_to_caseI_endpoint_provider
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D : ℕ} {d Δ C1 Θ K C145 : ℝ}
    (hN2 : 2 ≤ N)
    (hOddBoundary : Odd N →
      ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ ^ 3 ≤ D)
    (hclaim : Claim14_5Regime 2 (D : ℝ) (sourceSigma (D : ℝ) d)
        C1 K Θ (sourceSigma (D : ℝ) d) →
      ActualClaim145BoundAt S H N D d Δ K
        (sourceSigma (D : ℝ) d) C145) :
    Claim14_5Regime 2 (D : ℝ) (sourceSigma (D : ℝ) d)
        C1 K Θ (sourceSigma (D : ℝ) d) →
      (∑ p ∈ suzukiSupportedBelow S
          ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤
        C145 * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := by
  intro hregime
  have hcar : sourceParityIndices (N - 1) =
      suzukiActualParityCarrier (N - 1) := by
    ext m
    simp only [sourceParityIndices, suzukiActualParityCarrier,
      Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, hpar⟩
      exact ⟨by omega, hm1, hpar⟩
    · rintro ⟨hmN, hm1, hpar⟩
      exact ⟨⟨hm1, by omega⟩, hpar⟩
  have hrec := suzukiActualT_caseI_recurrence (S := S) hN2 hOddBoundary
  have hsum :
      (∑ p ∈ suzukiSupportedBelow S
          ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) =
        suzukiActualT S N D
          ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ := by
    rw [hcar]
    simp_rw [← suzukiActualT_eq_parity_sum]
    exact hrec.symm
  rw [hsum]
  exact hclaim hregime


end MathlibNt.SieveTheory
