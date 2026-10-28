import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseABoundedK
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseALowSFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAHighSFinal

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


end MathlibNt.SieveTheory
