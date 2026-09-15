import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053MinusFirstCrossing
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiConstruction

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Topological producer for a genuine minus first crossing

The crossing is the least point of the nonempty compact set on which the
normalized minus slope reaches `c`.
-/

namespace Section10MinusFirstCrossingProducer

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053MinusFirstCrossing
open Section10CanonicalXi

/-- The normalized minus base is continuous at every point strictly to the
right of the apparatus threshold. -/
lemma normalizedMinusBase_continuousAt
    {R : ℝ → ℝ} {β s : ℝ} (h : FirstCrossingDDEApparatus R β)
    (hβs : β < s) :
    ContinuousAt (normalizedMinusBase R xi) s := by
  have hsR : β - 1 < s := by linarith
  have hsmR : β - 1 < s - 1 := by linarith
  have hs0 : s ≠ 0 := by linarith [h.beta_ge_one]
  have hRs : 0 < R s := h.positive s hsR
  have hRc : ContinuousAt R s :=
    h.continuous.continuousAt (Ioi_mem_nhds hsR)
  have hRmc : ContinuousAt (fun u : ℝ => R (u - 1)) s :=
    (h.continuous.continuousAt (Ioi_mem_nhds hsmR)).comp_of_eq
      (continuousAt_id.sub continuousAt_const) (by simp)
  exact (((hRmc.neg.div (continuousAt_id.mul hRc)
    (mul_ne_zero hs0 (ne_of_gt hRs))).add xi_continuous.continuousAt).sub
      (continuousAt_const.div continuousAt_id hs0))

/-- If the normalized base starts strictly below `c` and reaches `c` by `v`,
the least point of the closed crossing set is a genuine first crossing.

`hDDEβ` is the endpoint derivative required literally by the current
`MinusFirstCrossing.hasDeriv` field.  The apparatus itself supplies the DDE only
for `β < u`, so this one endpoint cannot be inferred from that interface. -/
theorem minusFirstCrossing_of_reaches
    {R : ℝ → ℝ} {β c S v : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hβS : β < S) (hβoneS : β + 1 ≤ S)
    (hinitial : ∀ u ∈ Icc β S, normalizedMinusBase R xi u < c)
    (hSv : S ≤ v) (hv : c ≤ normalizedMinusBase R xi v) :
    ∃ w : MinusFirstCrossing R xi c β S, S ≤ w.s := by
  let f : ℝ → ℝ := normalizedMinusBase R xi
  let K : Set ℝ := Icc S v ∩ f ⁻¹' Ici c
  have hfcont : ContinuousOn f (Icc S v) := by
    intro u hu
    exact (normalizedMinusBase_continuousAt h (hβS.trans_le hu.1)).continuousWithinAt
  have hKclosed : IsClosed K :=
    hfcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hKcompact : IsCompact K :=
    isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
  have hvK : v ∈ K := by
    exact ⟨⟨hSv, le_rfl⟩, hv⟩
  obtain ⟨s, hsK, hsleast⟩ := hKcompact.exists_isLeast ⟨v, hvK⟩
  have hSs : S ≤ s := hsK.1.1
  have hsv : s ≤ v := hsK.1.2
  have hcross : c ≤ f s := hsK.2
  have hSlt : S < s := by
    apply lt_of_le_of_ne hSs
    intro hEq
    have hfs : f S < c := hinitial S ⟨hβS.le, le_rfl⟩
    rw [← hEq] at hcross
    exact (not_le_of_gt hfs) hcross
  let slope : ℝ → ℝ := fun u => f u - c
  have hslope_cont : ContinuousAt slope s := by
    exact (normalizedMinusBase_continuousAt h (hβS.trans hSlt)).sub continuousAt_const
  have hlogCont : ContinuousOn (logEnvelopeMinus R xi c) (Icc β s) := by
    intro u hu
    have huR : β - 1 < u := by linarith [hu.1]
    have hRu : 0 < R u := h.positive u huR
    have hRc : ContinuousAt R u :=
      h.continuous.continuousAt (Ioi_mem_nhds huR)
    exact ((hRc.log (ne_of_gt hRu)).add
      (xiPhase_hasDerivAt canonicalXi_proposition1020 u).continuousAt |>.sub
        ((hasDerivAt_id u).const_mul c).continuousAt).continuousWithinAt
  have hderiv : ∀ u ∈ Ioc β s,
      HasDerivAt (logEnvelopeMinus R xi c) (slope u) u := by
    intro u hu
    have hβ0 : 0 < β := zero_lt_one.trans_le h.beta_ge_one
    have hu0 : 0 < u := hβ0.trans hu.1
    have hRu : 0 < R u := h.positive u
      ((sub_lt_self β one_pos).trans hu.1)
    have hdde : HasDerivAt R (-(2 * R u + R (u - 1)) / u) u :=
      h.original_dde u hu.1
    have hlog := lemma1028_logEnvelopeMinus_hasDerivAt
      canonicalXi_proposition1020 (c := c) hu0 hRu hdde
    convert hlog using 1
    dsimp [slope, f, normalizedMinusBase]
    ring
  have hinitialSlope : ∀ u ∈ Icc β S, slope u < 0 := by
    intro u hu
    dsimp [slope, f]
    linarith [hinitial u hu]
  have hbefore : ∀ u, S < u → u < s → slope u < 0 := by
    intro u hSu hus
    have huv : u ≤ v := le_trans hus.le hsv
    have hnotK : u ∉ K := by
      intro huK
      exact (not_le_of_gt hus) (hsleast huK)
    have hfc : f u < c := by
      by_contra hn
      have hcf : c ≤ f u := le_of_not_gt hn
      exact hnotK ⟨⟨hSu.le, huv⟩, hcf⟩
    dsimp [slope]
    linarith
  have hcrossSlope : 0 ≤ slope s := by
    dsimp [slope]
    exact sub_nonneg.mpr hcross
  let w : MinusFirstCrossing R xi c β S :=
    { s := s
      slope := slope
      beta_lt_s₀ := hβS
      s₀_lt_s := hSlt
      beta_add_one_le_s := hβoneS.trans hSs
      slope_continuousAt := hslope_cont
      log_continuousOn := hlogCont
      hasDeriv := hderiv
      initial_neg := hinitialSlope
      before_crossing_neg := hbefore
      crossing_nonneg := hcrossSlope }
  exact ⟨w, hSs⟩

/-- Pointwise crossing production, in the exact shape consumed by
`ProducesMinusFirstCrossing` after unfolding that definition. -/
theorem producesMinusFirstCrossing
    {R : ℝ → ℝ} {β c S : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hβS : β < S) (hβoneS : β + 1 ≤ S)
    (hinitial : ∀ u ∈ Icc β S, normalizedMinusBase R xi u < c) :
    ∀ v, S ≤ v → c ≤ normalizedMinusBase R xi v →
      ∃ w : MinusFirstCrossing R xi c β S, S ≤ w.s := by
  intro v hSv hv
  exact minusFirstCrossing_of_reaches h hβS hβoneS hinitial hSv hv


end Section10MinusFirstCrossingProducer
