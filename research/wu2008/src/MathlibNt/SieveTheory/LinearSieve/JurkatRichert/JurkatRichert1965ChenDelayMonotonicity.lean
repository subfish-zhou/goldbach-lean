import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965ChenDelayFunctions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact

/-!
# Order properties of the constructed Jurkat--Richert delay functions

The weighted difference satisfies the Dickman renewal identity. Its positivity
gives the order and monotonicity statements in Jurkat--Richert (1965), (5.11)--(5.13).
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The weighted upper-minus-lower difference of the actual finite-step solution. -/
def delayDifference (A : ℝ) (u : ℝ) : ℝ :=
  delayWeight A false u - delayWeight A true u

theorem continuous_delayDifference (A : ℝ) : Continuous (delayDifference A) :=
  (continuous_delayWeight A false).sub (continuous_delayWeight A true)

theorem delayDifference_initial (A : ℝ) {u : ℝ} (hu : u ≤ 2) :
    delayDifference A u = A := by
  simp [delayDifference, delayWeight_initial A _ hu, delayInitial]

theorem hasDerivAt_delayDifference (A : ℝ) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (delayDifference A) (-delayDifference A (u - 1) / (u - 1)) u := by
  apply ((hasDerivAt_delayWeight A false hu).sub
    (hasDerivAt_delayWeight A true hu)).congr_deriv
  simp only [Bool.not_false, Bool.not_true, delayFunction, delayDifference]
  ring

/-- The renewal identity, including its initial endpoint. -/
theorem delayDifference_renewal (A : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    (u - 1) * delayDifference A u = ∫ t in (u - 1)..u, delayDifference A t := by
  let P : ℝ → ℝ := fun x => ∫ t in (1 : ℝ)..x, delayDifference A t
  let R : ℝ → ℝ := fun x => (x - 1) * delayDifference A x - (P x - P (x - 1))
  have hc := continuous_delayDifference A
  have hP : Continuous P := intervalIntegral.continuous_primitive
    (fun a b => hc.intervalIntegrable a b) 1
  have hR : Continuous R := ((continuous_id.sub continuous_const).mul hc).sub
    (hP.sub (hP.comp (continuous_id.sub continuous_const)))
  have hd (x : ℝ) (hx : x ∈ interior (Icc 2 u)) : HasDerivAt R 0 x := by
    rw [interior_Icc] at hx
    have hdx := hasDerivAt_delayDifference A hx.1
    have hp := (hc.integral_hasStrictDerivAt 1 x).hasDerivAt
    have hq := ((hc.integral_hasStrictDerivAt 1 (x - 1)).hasDerivAt).comp x
      ((hasDerivAt_id x).sub_const 1)
    apply ((((hasDerivAt_id x).sub_const 1).mul hdx).sub (hp.sub hq)).congr_deriv
    dsimp
    field_simp [ne_of_gt (show 0 < x - 1 by linarith [hx.1])]
    ring
  have hanti : AntitoneOn R (Icc 2 u) := antitoneOn_of_deriv_nonpos (convex_Icc ..)
    hR.continuousOn (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv.le)
  have hmono : MonotoneOn R (Icc 2 u) := monotoneOn_of_deriv_nonneg (convex_Icc ..)
    hR.continuousOn (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv.ge)
  have heq : R u = R 2 := le_antisymm
    (hanti ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu)
    (hmono ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu)
  have hi : P 2 = A := by
    change (∫ t in (1 : ℝ)..2, delayDifference A t) = A
    calc
      _ = ∫ _t in (1 : ℝ)..2, A := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact delayDifference_initial A (by
          have := (uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2) ▸ ht).2
          exact this)
      _ = A := by norm_num
  have hbase : R 2 = 0 := by
    dsimp [R]
    rw [delayDifference_initial A le_rfl, hi]
    norm_num [P]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 1 (u - 1)) (hc.intervalIntegrable (u - 1) u)
  rw [hbase] at heq
  dsimp [R, P] at heq
  linarith

private theorem exists_first_zero_on {H : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn H (Icc a b)) (ha : 0 < H a) (hb : H b ≤ 0) :
    ∃ c ∈ Ioc a b, H c = 0 ∧ ∀ x ∈ Ico a c, 0 < H x := by
  have hex : ∃ x ∈ Icc a b, H x = 0 :=
    intermediate_value_Icc' hab hc ⟨hb, ha.le⟩
  let S := Icc a b ∩ H ⁻¹' ({0} : Set ℝ)
  have hclosed : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  have hne : S.Nonempty := by
    rcases hex with ⟨x, hx, hz⟩
    exact ⟨x, hx, hz⟩
  obtain ⟨c, hcS, hmin⟩ := hcompact.exists_isMinOn hne continuous_id.continuousOn
  have hcz : H c = 0 := hcS.2
  have hac : a < c := lt_of_le_of_ne hcS.1.1 (by
    intro h
    rw [← h] at hcz
    linarith)
  refine ⟨c, ⟨hac, hcS.1.2⟩, hcz, ?_⟩
  intro x hx
  by_contra hpos
  have hxnonpos : H x ≤ 0 := le_of_not_gt hpos
  obtain ⟨y, hy, hyz⟩ := intermediate_value_Icc' hx.1
    (hc.mono (Icc_subset_Icc le_rfl (hx.2.le.trans hcS.1.2))) ⟨hxnonpos, ha.le⟩
  have hcy : c ≤ y := hmin ⟨⟨hy.1, hy.2.trans (hx.2.le.trans hcS.1.2)⟩, hyz⟩
  linarith [hy.2, hx.2]

/-- Strict positivity of the weighted difference, by its renewal identity. -/
theorem delayDifference_pos {A : ℝ} (hA : 0 < A) (u : ℝ) :
    0 < delayDifference A u := by
  by_cases hu : u ≤ 2
  · simpa [delayDifference_initial A hu] using hA
  by_contra hpos
  have hu' : 2 ≤ u := (lt_of_not_ge hu).le
  obtain ⟨c, hc, hzero, hbefore⟩ := exists_first_zero_on hu'
    (continuous_delayDifference A).continuousOn
    (by simpa [delayDifference_initial A le_rfl] using hA) (le_of_not_gt hpos)
  have hposbefore (t : ℝ) (ht : t < c) : 0 < delayDifference A t := by
    by_cases ht2 : t ≤ 2
    · simpa [delayDifference_initial A ht2] using hA
    · exact hbefore t ⟨(lt_of_not_ge ht2).le, ht⟩
  have hint : 0 < ∫ t in (c - 1)..c, delayDifference A t := by
    apply intervalIntegral.integral_pos (by linarith) (continuous_delayDifference A).continuousOn
    · intro t ht
      rcases ht.2.eq_or_lt with h | h
      · rw [h, hzero]
      · exact (hposbefore t h).le
    · exact ⟨c - 1, ⟨le_rfl, by linarith⟩, hposbefore _ (by linarith)⟩
  have hrenew := delayDifference_renewal A hc.1.le
  rw [hzero, mul_zero] at hrenew
  linarith

/-- The strict gap (5.11), for the constructed pair and positive normalization. -/
theorem delayFunction_lower_lt_upper {A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    delayFunction A true u < delayFunction A false u := by
  have h := delayDifference_pos hA u
  exact (div_lt_div_iff_of_pos_right hu).2 (sub_pos.mp h)

theorem jr1965f_lt_jr1965F {u : ℝ} (hu : 0 < u) : jr1965f u < jr1965F u :=
  delayFunction_lower_lt_upper (by unfold jr1965DelayConstant; positivity) hu

/-- The unweighted differential equation on the open delay range. -/
theorem hasDerivAt_delayFunction (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (delayFunction A b)
      ((delayFunction A (!b) (u - 1) - delayFunction A b u) / u) u := by
  apply ((hasDerivAt_delayWeight A b hu).div (hasDerivAt_id u)
    (ne_of_gt (show 0 < u by linarith))).congr_deriv
  dsimp [delayFunction]
  field_simp

theorem hasDerivAt_jr1965F {u : ℝ} (hu : 2 < u) :
    HasDerivAt jr1965F ((jr1965f (u - 1) - jr1965F u) / u) u :=
  hasDerivAt_delayFunction jr1965DelayConstant false hu

theorem hasDerivAt_jr1965f {u : ℝ} (hu : 2 < u) :
    HasDerivAt jr1965f ((jr1965F (u - 1) - jr1965f u) / u) u :=
  hasDerivAt_delayFunction jr1965DelayConstant true hu

private theorem hasDerivAt_jr1965F_initial {u : ℝ} (hu : 0 < u) (hu3 : u < 3) :
    HasDerivAt jr1965F (-jr1965DelayConstant / u ^ 2) u := by
  have hd := (hasDerivAt_const u jr1965DelayConstant).div
    (hasDerivAt_id u) (ne_of_gt hu)
  have hd' : HasDerivAt (fun x : ℝ => jr1965DelayConstant / x)
      (-jr1965DelayConstant / u ^ 2) u := hd.congr_deriv (by simp)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hu3] with x hx
  exact jr1965F_eq_of_le_three hx.le

private theorem jr1965F_antitoneOn_before {c : ℝ}
    (hbefore : ∀ x ∈ Ico 3 c, jr1965f (x - 1) < jr1965F x) :
    AntitoneOn jr1965F (Ioc 0 c) := by
  have hd (x : ℝ) (hx : x ∈ interior (Ioc 0 c)) :
      DifferentiableAt ℝ jr1965F x ∧ deriv jr1965F x ≤ 0 := by
    rw [interior_Ioc] at hx
    by_cases hx2 : x ≤ 2
    · have h := hasDerivAt_jr1965F_initial hx.1 (by linarith)
      refine ⟨h.differentiableAt, ?_⟩
      rw [h.deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by
        unfold jr1965DelayConstant; positivity))
        (sq_nonneg x)
    · have hx2' : 2 < x := lt_of_not_ge hx2
      have h := hasDerivAt_jr1965F hx2'
      refine ⟨h.differentiableAt, ?_⟩
      rw [h.deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ hx.1.le
      apply sub_nonpos.mpr
      by_cases hx3 : x ≤ 3
      · rw [jr1965f_initial (by linarith)]
        exact (jr1965F_pos hx.1).le
      · exact (hbefore x ⟨(lt_of_not_ge hx3).le, hx.2⟩).le
  exact antitoneOn_of_deriv_nonpos (convex_Ioc ..)
    (continuousOn_jr1965F.mono (fun _ hx => hx.1))
    (fun x hx => (hd x hx).1.differentiableWithinAt) (fun x hx => (hd x hx).2)

private theorem jr1965f_monotoneOn_of_upper_antitone {c : ℝ}
    (hF : AntitoneOn jr1965F (Ioc 0 c)) : MonotoneOn jr1965f (Icc 2 c) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc ..)
    (continuousOn_jr1965f.mono (fun _ hx => lt_of_lt_of_le (by norm_num) hx.1))
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_jr1965f hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_jr1965f hx.1).deriv]
    apply div_nonneg _ (by linarith [hx.1])
    apply sub_nonneg.mpr
    exact (jr1965f_lt_jr1965F (by linarith [hx.1])).le.trans
      (hF ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ⟨by linarith [hx.1], hx.2.le⟩ (by linarith))

/-- The delayed lower function stays strictly below the current upper function.
At a first failure, the upper function is decreasing up to that point, hence the
lower one is increasing, contradicting the strict upper/lower gap. -/
theorem jr1965f_sub_one_lt_jr1965F {u : ℝ} (hu : 2 ≤ u) :
    jr1965f (u - 1) < jr1965F u := by
  by_cases hu3 : u ≤ 3
  · rw [jr1965f_initial (by linarith)]
    exact jr1965F_pos (by linarith)
  let H : ℝ → ℝ := fun x => jr1965F x - jr1965f (x - 1)
  have hcont : ContinuousOn H (Icc 3 u) := by
    apply (continuousOn_jr1965F.mono (fun _ hx =>
      lt_of_lt_of_le (by norm_num) hx.1)).sub
    exact continuousOn_jr1965f.comp (continuousOn_id.sub continuousOn_const)
      (fun x hx => by change 0 < x - 1; linarith [hx.1])
  have h3 : 0 < H 3 := by
    dsimp [H]
    rw [jr1965f_initial (by norm_num), sub_zero]
    exact jr1965F_pos (by norm_num)
  by_contra h
  have huH : H u ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
  obtain ⟨c, hc, hzero, hbefore⟩ :=
    exists_first_zero_on (lt_of_not_ge hu3).le hcont h3 huH
  have hF := jr1965F_antitoneOn_before
    (fun x hx => sub_pos.mp (hbefore x hx))
  have hf := jr1965f_monotoneOn_of_upper_antitone hF
  have hf' : jr1965f (c - 1) ≤ jr1965f c :=
    hf ⟨by linarith [hc.1], by linarith⟩
      ⟨by linarith [hc.1], le_rfl⟩ (by linarith)
  have hgap := jr1965f_lt_jr1965F (show 0 < c by linarith [hc.1])
  dsimp [H] at hzero
  linarith

/-- The upper function is decreasing on the entire positive half-line. -/
theorem antitoneOn_jr1965F : AntitoneOn jr1965F (Ioi 0) := by
  intro x hx y hy hxy
  exact jr1965F_antitoneOn_before
    (fun z hz => jr1965f_sub_one_lt_jr1965F (by linarith [hz.1]))
    ⟨hx, hxy⟩ ⟨hy, le_rfl⟩ hxy

/-- The lower function is increasing on the entire positive half-line. -/
theorem monotoneOn_jr1965f : MonotoneOn jr1965f (Ioi 0) := by
  intro x hx y hy hxy
  by_cases hx2 : x ≤ 2
  · rw [jr1965f_initial hx2]
    exact jr1965f_nonneg hy
  · exact jr1965f_monotoneOn_of_upper_antitone
      (antitoneOn_jr1965F.mono (fun _ hz => hz.1))
      ⟨(lt_of_not_ge hx2).le, hxy⟩ ⟨by linarith, le_rfl⟩ hxy

theorem deriv_jr1965F_neg {u : ℝ} (hu : 0 < u) : deriv jr1965F u < 0 := by
  by_cases hu2 : u ≤ 2
  · rw [(hasDerivAt_jr1965F_initial hu (by linarith)).deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by
      unfold jr1965DelayConstant; positivity)) (sq_pos_of_pos hu)
  · rw [(hasDerivAt_jr1965F (lt_of_not_ge hu2)).deriv]
    exact div_neg_of_neg_of_pos
      (sub_neg.mpr (jr1965f_sub_one_lt_jr1965F (lt_of_not_ge hu2).le)) hu

theorem deriv_jr1965f_pos {u : ℝ} (hu : 2 < u) : 0 < deriv jr1965f u := by
  rw [(hasDerivAt_jr1965f hu).deriv]
  apply div_pos _ (by linarith)
  apply sub_pos.mpr
  exact (jr1965f_lt_jr1965F (by linarith)).trans_le
    (antitoneOn_jr1965F (by change 0 < u - 1; linarith)
      (by change 0 < u; linarith) (by linarith))

theorem jr1965F_le_delayConstant {u : ℝ} (hu : 1 ≤ u) :
    jr1965F u ≤ jr1965DelayConstant := by
  have h := antitoneOn_jr1965F (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show u ∈ Ioi 0 from lt_of_lt_of_le zero_lt_one hu) hu
  simpa [jr1965F_initial (by norm_num : (1 : ℝ) ≤ 2), jr1965DelayConstant] using h

theorem jr1965f_le_delayConstant {u : ℝ} (hu : 1 ≤ u) :
    jr1965f u ≤ jr1965DelayConstant :=
  (jr1965f_lt_jr1965F (lt_of_lt_of_le zero_lt_one hu)).le.trans
    (jr1965F_le_delayConstant hu)

theorem jr1965g_nonneg (ν : ℕ) {u : ℝ} (hu : 0 < u) : 0 ≤ jr1965g ν u := by
  unfold jr1965g
  split_ifs
  · exact (jr1965F_pos hu).le
  · exact jr1965f_nonneg hu

theorem jr1965g_le_delayConstant (ν : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    jr1965g ν u ≤ jr1965DelayConstant := by
  unfold jr1965g
  split_ifs
  · exact jr1965F_le_delayConstant hu
  · exact jr1965f_le_delayConstant hu

theorem abs_jr1965g_le_delayConstant (ν : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |jr1965g ν u| ≤ jr1965DelayConstant := by
  rw [abs_of_nonneg (jr1965g_nonneg ν (lt_of_lt_of_le zero_lt_one hu))]
  exact jr1965g_le_delayConstant ν hu

/-- Uniform total variation on the entire unbounded sieve range. In particular,
the bound does not depend on either endpoint of a finite subinterval. -/
theorem eVariationOn_jr1965g_Ici_le (ν : ℕ) :
    eVariationOn (jr1965g ν) (Ici 1) ≤ ENNReal.ofReal jr1965DelayConstant := by
  have hid : eVariationOn (id : ℝ → ℝ) (Icc 0 jr1965DelayConstant) =
      ENNReal.ofReal jr1965DelayConstant := by
    simp [eVariationOn_id_Icc]
  have hmapsF : MapsTo jr1965F (Ici 1) (Icc 0 jr1965DelayConstant) :=
    fun _ hx => ⟨(jr1965F_pos (lt_of_lt_of_le zero_lt_one hx)).le,
      jr1965F_le_delayConstant hx⟩
  have hmapsf : MapsTo jr1965f (Ici 1) (Icc 0 jr1965DelayConstant) :=
    fun _ hx => ⟨jr1965f_nonneg (lt_of_lt_of_le zero_lt_one hx),
      jr1965f_le_delayConstant hx⟩
  unfold jr1965g
  split_ifs
  · simpa only [Function.id_comp, hid] using
      eVariationOn.comp_le_of_antitoneOn (id : ℝ → ℝ) jr1965F
        (t := Ici 1) (s := Icc 0 jr1965DelayConstant)
        (antitoneOn_jr1965F.mono (fun _ hx => lt_of_lt_of_le zero_lt_one hx)) hmapsF
  · simpa only [Function.id_comp, hid] using
      eVariationOn.comp_le_of_monotoneOn (id : ℝ → ℝ) jr1965f
        (t := Ici 1) (s := Icc 0 jr1965DelayConstant)
        (monotoneOn_jr1965f.mono (fun _ hx => lt_of_lt_of_le zero_lt_one hx)) hmapsf

theorem boundedVariationOn_jr1965g_Ici (ν : ℕ) :
    BoundedVariationOn (jr1965g ν) (Ici 1) :=
  ne_of_lt ((eVariationOn_jr1965g_Ici_le ν).trans_lt ENNReal.ofReal_lt_top)

theorem eVariationOn_jr1965g_Icc_le (ν : ℕ) {a b : ℝ} (ha : 1 ≤ a) :
    eVariationOn (jr1965g ν) (Icc a b) ≤ ENNReal.ofReal jr1965DelayConstant :=
  (eVariationOn.mono _ (fun _ hx => ha.trans hx.1)).trans (eVariationOn_jr1965g_Ici_le ν)

end MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
