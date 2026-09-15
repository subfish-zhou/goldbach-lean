import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIRawRoundedFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIOddFinalClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144FullFiniteDepthFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

/-- The Case-II side used by the finite-depth partition: odd depth and the
closed low strip.  At even depth this side is empty. -/
def Lemma144CaseIIFinalSide (N : ℕ) (s : ℝ) : Prop :=
  Odd N ∧ s ≤ 3

/-- Direct odd Case-II same-`C` closure with the genuine global predecessor IH.
The raw rounded estimate and Claim-14.5 endpoint normalization are combined at
one eventual cutoff; no IH-free raw-producer abstraction is used. -/
theorem eventually_lemma144_caseII_odd_sameC_final
    (S : BoundingSieve) (H : Section13HatLayers)
    {Dmin N : ℕ} {d Δ C K C145 : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hC3 : 3 ≤ C) (hK : 2 ≤ K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hDmin : 2 ≤ Dmin)
    (hN : Odd N) (hN3 : 3 ≤ N) :
    ∀ᶠ D : ℕ in atTop, ∀ s : ℝ,
      1 < s → s ≤ 3 →
      Lemma144GlobalDepthAt S H C K d Δ (N - 1) Dmin →
      Lemma144CaseIISameCAt S H N D d Δ C K s := by
  have hraw := eventually_lemma144_caseII_odd_rawRoundedFinal
    S H hH hd1 hΔ0 hΔ1 hC3 hK hlocal hDmin
  have hscale : Lemma144CaseIIOddClaim145ScalingBridge S H d Δ C K C145 :=
    lemma144_caseII_odd_claim145_scaling_bridge S H hH hd1 hΔ0 hΔ1 hd
      (by linarith) (by linarith) hC145
  have hnormalize : Lemma144CaseIIOddEndpointGapNormalization S H
      (caseIIOddClaim145Endpoint S d) d Δ C K :=
    lemma144_caseII_odd_endpoint_gap_of_claim145_scaling_bridge S H
      hΔ0 hΔ1 hd (by linarith) hC145 hlocal hH hscale
  obtain ⟨Dn, _hDn1, hn⟩ := hnormalize N hN hN3
  have hDn : ∀ᶠ D : ℕ in atTop, Dn ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Dn)
  filter_upwards [hraw, hDn] with D hrawD hDnD
  intro s hs1 hs3 hIH
  have hrelative := hrawD N s hN hN3 hs1 hs3 hIH
  have hgap := hn D hDnD s hs1 hs3
  dsimp at hgap
  dsimp [Lemma144CaseIISameCAt]
  simpa [sourceParityIndices] using
    (caseII_sameC_of_relative_and_endpoint_gap
      (scale := C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ))
      (bracket := caseIIConcreteRoundedRelativeBracket N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) C K)
      hgap hrelative)

/-- Exact `hcaseII` packet expected by `lemma14_4_full_finiteDepth_final`.
For a successor depth, the Case-II side is impossible when the successor is
even; when it is odd, `N+1 ≥ 3` and the direct global-IH theorem applies. -/
theorem lemma14_4_caseII_final_finiteDepth_interface
    (S : BoundingSieve) (H : Section13HatLayers)
    {C K d Δ C145 : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hC3 : 3 ≤ C) (hK : 2 ≤ K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ N Dmin : ℕ,
      1 ≤ N → 2 ≤ Dmin →
      Lemma144GlobalDepthAt S H C K d Δ N Dmin →
      ∃ DII : ℕ, Dmin ≤ DII ∧
        Lemma144UniformNatCeilRestrictedAt S H C K d Δ (N + 1) DII
          (Lemma144CaseIIFinalSide (N + 1)) := by
  intro N Dmin hN hDmin hIH
  by_cases hodd : Odd (N + 1)
  · have hN3 : 3 ≤ N + 1 := by
      have hN2 : 2 ≤ N + 1 := by omega
      have hmod : (N + 1) % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    have hevent := eventually_lemma144_caseII_odd_sameC_final
      S H hH hd1 hΔ0 hΔ1 hd hC3 hK hC145 hlocal hDmin hodd hN3
    obtain ⟨D0, hD0⟩ := eventually_atTop.1 hevent
    refine ⟨max Dmin D0, le_max_left _ _, ?_⟩
    intro D hD hD2 s hs ⟨_hsOdd, hs3⟩ hz2
    have hpred : Lemma144GlobalDepthAt S H C K d Δ ((N + 1) - 1) Dmin := by
      simpa [Nat.add_sub_cancel] using hIH
    have hsame := hD0 D ((le_max_right Dmin D0).trans hD) s
      (by
        have hmod : (N + 1) % 2 = 1 := Nat.odd_iff.mp hodd
        have hs' : (2 : ℝ) - 1 < s := by
          simpa [KappaOneModel.parityDomain, hmod] using hs
        norm_num at hs' ⊢
        exact hs')
      hs3 hpred
    dsimp [Lemma144CaseIISameCAt] at hsame
    rw [suzukiActualT_eq_parity_sum]
    have hcarrier : suzukiActualParityCarrier (N + 1) =
        (Finset.Icc 1 (N + 1)).filter (fun n => n % 2 = (N + 1) % 2) := by
      ext n
      simp [suzukiActualParityCarrier]
      omega
    rw [hcarrier]
    exact hsame
  · refine ⟨Dmin, le_rfl, ?_⟩
    intro D _hD _hD2 s _hs hsII _hz2
    exact False.elim (hodd hsII.1)

/-- The same packet with the unused finite-depth bound binders, ready to pass
literally as `hcaseII` to `lemma14_4_full_finiteDepth_final`. -/
theorem lemma14_4_caseII_final_hcaseII
    (S : BoundingSieve) (H : Section13HatLayers)
    {C K d Δ C145 : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hC3 : 3 ≤ C) (hK : 2 ≤ K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ depth N Dmin : ℕ,
      1 ≤ N → N < depth → 2 ≤ Dmin →
      Lemma144GlobalDepthAt S H C K d Δ N Dmin →
      ∃ DII : ℕ, Dmin ≤ DII ∧
        Lemma144UniformNatCeilRestrictedAt S H C K d Δ (N + 1) DII
          (Lemma144CaseIIFinalSide (N + 1)) := by
  intro _depth N Dmin hN _hNdepth hDmin hIH
  exact lemma14_4_caseII_final_finiteDepth_interface S H hH hd1 hΔ0 hΔ1 hd
    hC3 hK hC145 hlocal N Dmin hN hDmin hIH


end MathlibNt.SieveTheory
