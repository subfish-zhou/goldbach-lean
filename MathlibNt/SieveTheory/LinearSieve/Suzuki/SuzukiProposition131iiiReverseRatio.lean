import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13BridgeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiQuantitativeDerivatives

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

open BridgeAssembly
open Section10CanonicalXi

/-!
# Uniform reverse adjacent ratio for the `Σ₁₂` endpoint

The missing direction is the upper bound for the earlier, opposite-sign layer
relative to the current layer.  The source of this direction is the increasing
`W₊` half of Lemma 10.28.  We freeze that earliest analytic edge below in its
multiplied (10.44) form; no adjacent-value quotient is a field of the edge.
-/

/-- The increasing-envelope half of Lemma 10.28, specialized to
`DDE(2,1,3)`.  By (10.44), this is exactly `(log W₊)' ≥ 0` after multiplication
by the positive value `s * R s`.  The constants precede the moving variable. -/
def Section10Lemma1028ReverseEnvelopeEdge (R : ℝ → ℝ) : Prop :=
  ∃ c S : ℝ, 1 ≤ c ∧ Real.exp 2 ≤ S ∧ 4 ≤ S ∧ ∀ s : ℝ, S ≤ s →
    0 ≤ -R (s - 1) + s * (xi s + c - 2 / s) * R s

private lemma xi_sub_two_log_antitone_exp_two :
    AntitoneOn (fun s : ℝ => xi s - 2 * Real.log s) (Ici (Real.exp 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (Real.exp 2))
  · apply xi_continuous.continuousOn.sub
    intro s hs
    exact (Real.continuousAt_log (ne_of_gt ((Real.exp_pos 2).trans_le hs))).const_mul 2
      |>.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hspos : 0 < s := (Real.exp_pos 2).trans hs
    have hs1 : 1 < s :=
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans hs
    exact ((xi_hasDerivAt hs1).differentiableAt.sub
      ((Real.hasDerivAt_log (ne_of_gt hspos)).const_mul 2).differentiableAt).differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs' : Real.exp 2 ≤ s := hs.le
    have hspos : 0 < s := (Real.exp_pos 2).trans_le hs'
    have hs1 : 1 < s :=
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hs'
    have hderiv : deriv (fun u : ℝ => xi u - 2 * Real.log u) s =
        deriv xi s - 2 / s := by
      have hd := ((xi_hasDerivAt hs1).sub
        ((Real.hasDerivAt_log (ne_of_gt hspos)).const_mul 2)).deriv
      have hfun : (xi - fun u : ℝ => 2 * Real.log u) =
          (fun u : ℝ => xi u - 2 * Real.log u) := by
        funext u
        rfl
      have hd' : deriv (fun u : ℝ => xi u - 2 * Real.log u) s =
          (xiSlope s)⁻¹ - 2 * s⁻¹ := by
        rw [← hfun]
        exact hd
      rw [hd', ← xi_deriv hs1]
      field_simp [ne_of_gt hspos]
    rw [hderiv]
    exact sub_nonpos.mpr (xi_deriv_le_two_div hs')

private lemma xi_le_two_log_add_exp_two {s : ℝ} (hs : Real.exp 2 ≤ s) :
    xi s ≤ xi (Real.exp 2) + 2 * Real.log s := by
  have h := xi_sub_two_log_antitone_exp_two
    (show Real.exp 2 ∈ Ici (Real.exp 2) by simp)
    (show s ∈ Ici (Real.exp 2) from hs) hs
  dsimp at h
  rw [Real.log_exp] at h
  linarith

/-- The canonical phase in the increasing-envelope edge is at most a fixed
multiple of `log (e s)`. -/
lemma canonicalXi_add_const_le_log_e_mul (c : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ s : ℝ, Real.exp 2 ≤ s →
      xi s + c - 2 / s ≤ A * Real.log (Real.exp 1 * s) := by
  let A : ℝ := 2 + |xi (Real.exp 2) + c|
  have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg (xi (Real.exp 2) + c)]
  refine ⟨A, hA, ?_⟩
  intro s hs
  have hspos : 0 < s := (Real.exp_pos 2).trans_le hs
  have hs1 : 1 ≤ s := by
    exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).le.trans hs
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hxi : xi s ≤ xi (Real.exp 2) + 2 * Real.log s := by
    exact xi_le_two_log_add_exp_two hs
  have habs : xi (Real.exp 2) + c ≤ |xi (Real.exp 2) + c| := le_abs_self _
  have hlogeq : Real.log (Real.exp 1 * s) = 1 + Real.log s := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hspos), Real.log_exp]
  rw [hlogeq]
  dsimp [A]
  have hdiv : 0 ≤ 2 / s := div_nonneg (by norm_num) hspos.le
  nlinarith [abs_nonneg (xi (Real.exp 2) + c)]

/-- Lemma 10.28's increasing envelope gives the missing direction of Lemma
10.29, uniformly after one fixed cutoff. -/
theorem section10_reverse_unitShift_after_cutoff
    {R : ℝ → ℝ} (hpos : ∀ s, 0 < s → 0 < R s)
    (hedge : Section10Lemma1028ReverseEnvelopeEdge R) :
    ∃ A S : ℝ, 1 ≤ A ∧ Real.exp 2 ≤ S ∧ 4 ≤ S ∧ ∀ s : ℝ, S ≤ s →
      R (s - 1) ≤ A * (s * Real.log (Real.exp 1 * s)) * R s := by
  rcases hedge with ⟨c, S, hc, hS, hS4, hedge⟩
  obtain ⟨A, hA, hxi⟩ := canonicalXi_add_const_le_log_e_mul c
  refine ⟨A, S, hA, hS, hS4, ?_⟩
  intro s hs
  have hsphase := hS.trans hs
  have hspos : 0 < s := (Real.exp_pos 2).trans_le hsphase
  have hRs : 0 ≤ R s := (hpos s hspos).le
  have hcoeff := hxi s hsphase
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoeff hspos.le) hRs
  have henv := hedge s hs
  nlinarith

/-- The literal opposite-earlier/current quotient required at the `Σ₁₂`
endpoint. -/
noncomputable def proposition131iiiReverseRatio
    (H : Section13HatLayers) (sign : ErrorSign) (s : ℝ) : ℝ :=
  H.T sign.opposite (s - 1) / H.T sign s

private lemma reverseRatio_continuousOn
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) (S : ℝ) :
    ContinuousOn (proposition131iiiReverseRatio H sign) (Icc 2 S) := by
  intro s hs
  have hspos : 0 < s := by linarith [hs.1]
  have hsmpos : 0 < s - 1 := by linarith [hs.1]
  have hnumAt : ContinuousAt (H.T sign.opposite) (s - 1) :=
    (hH.continuous sign.opposite).continuousAt (Ioi_mem_nhds hsmpos)
  have hnum : ContinuousAt (fun t : ℝ => H.T sign.opposite (t - 1)) s :=
    hnumAt.comp_of_eq (continuousAt_id.sub continuousAt_const) rfl
  have hden : ContinuousAt (H.T sign) s :=
    (hH.continuous sign).continuousAt (Ioi_mem_nhds hspos)
  exact (hnum.div hden (ne_of_gt (hH.positive sign s hspos))).continuousWithinAt

private theorem reverseRatio_compact_bound
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) (S : ℝ) :
    ∃ B : ℝ, ∀ s, s ∈ Icc (2 : ℝ) S →
      proposition131iiiReverseRatio H sign s ≤ B := by
  have hb := isCompact_Icc.bddAbove_image (reverseRatio_continuousOn hH sign S)
  rw [bddAbove_def] at hb
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, fun s hs => hB _ ⟨s, hs, rfl⟩⟩

/-- Source-faithful uniform reverse adjacent ratio.  A single constant works for
both signs and every moving endpoint `2 ≤ s ≤ σ`.  The only residual source
premise is the increasing-envelope half of Lemma 10.28 for the common `Qhat`;
compact coordinates are discharged by continuity and positivity. -/
theorem proposition131iii_uniform_reverse_adjacent_ratio
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (hedge : Section10Lemma1028ReverseEnvelopeEdge (section13Qhat H)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (sign : ErrorSign) (s σ : ℝ),
      2 ≤ s → s ≤ σ →
      proposition131iiiReverseRatio H sign s ≤
        C * (σ * Real.log (Real.exp 1 * σ)) := by
  obtain ⟨A, S, hA, hS, hS4, hshift⟩ :=
    section10_reverse_unitShift_after_cutoff
      (fun s hs => section13Qhat_pos hH.toSection13HatContract hs) hedge
  obtain ⟨Bp, hBp⟩ := reverseRatio_compact_bound hH.toSection13HatContract ErrorSign.plus S
  obtain ⟨Bm, hBm⟩ := reverseRatio_compact_bound hH.toSection13HatContract ErrorSign.minus S
  let K : ℝ := (section13_bridgeAtThree hH ErrorSign.plus).K
  let Ctail : ℝ := K ^ 2 * A
  let Ccompact : ℝ := max 1 (max Bp Bm)
  let C : ℝ := max Ctail Ccompact
  have hK1 : 1 ≤ K := (section13_bridgeAtThree hH ErrorSign.plus).one_le_K
  have hCtail1 : 1 ≤ Ctail := by
    dsimp [Ctail]
    nlinarith [sq_nonneg K]
  have hC1 : 1 ≤ C := hCtail1.trans (le_max_left _ _)
  refine ⟨C, hC1, ?_⟩
  intro sign s σ hs hsσ
  have hspos : 0 < s := by linarith
  have hσpos : 0 < σ := hspos.trans_le hsσ
  have hlogs : 0 < Real.log (Real.exp 1 * s) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hspos), Real.log_exp]
    have : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
    linarith
  have hlogσ : 0 < Real.log (Real.exp 1 * σ) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hσpos), Real.log_exp]
    have : 0 ≤ Real.log σ := Real.log_nonneg (by linarith)
    linarith
  have hlogmono : Real.log (Real.exp 1 * s) ≤ Real.log (Real.exp 1 * σ) :=
    Real.log_le_log (mul_pos (Real.exp_pos 1) hspos)
      (mul_le_mul_of_nonneg_left hsσ (Real.exp_pos 1).le)
  have hprodmono : s * Real.log (Real.exp 1 * s) ≤
      σ * Real.log (Real.exp 1 * σ) :=
    mul_le_mul hsσ hlogmono hlogs.le hσpos.le
  by_cases htail : S ≤ s
  · let B := section13_bridgeAtThree hH sign
    let Bopp := section13_bridgeAtThree hH sign.opposite
    have hs4 : 4 ≤ s := hS4.trans htail
    have hs3 : 3 ≤ s := by linarith
    have hsm3 : 3 ≤ s - 1 := by linarith
    have hQshift := hshift s htail
    have hK0 : 0 ≤ K := zero_le_one.trans hK1
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    have hfactor0 : 0 ≤ A * (s * Real.log (Real.exp 1 * s)) :=
      mul_nonneg hA0 (mul_nonneg hspos.le hlogs.le)
    have hraw : H.T sign.opposite (s - 1) ≤
        Ctail * (s * Real.log (Real.exp 1 * s)) * H.T sign s := by
      calc
        H.T sign.opposite (s - 1) ≤ Bopp.K * Bopp.Qhat (s - 1) := Bopp.hat_le (s - 1) hsm3
        _ ≤ Bopp.K * (A * (s * Real.log (Real.exp 1 * s)) * B.Qhat s) := by
          apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans Bopp.one_le_K)
          change section13Qhat H (s - 1) ≤
            A * (s * Real.log (Real.exp 1 * s)) * section13Qhat H s
          exact hQshift
        _ ≤ Bopp.K * (A * (s * Real.log (Real.exp 1 * s)) *
            (B.K * H.T sign s)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left (B.Q_le s hs3) hfactor0
          · exact zero_le_one.trans Bopp.one_le_K
        _ = Ctail * (s * Real.log (Real.exp 1 * s)) * H.T sign s := by
          change Bopp.K * (A * (s * Real.log (Real.exp 1 * s)) *
            (B.K * H.T sign s)) = K ^ 2 * A *
              (s * Real.log (Real.exp 1 * s)) * H.T sign s
          have hKB : B.K = K := by cases sign <;> rfl
          have hKBopp : Bopp.K = K := by cases sign <;> rfl
          rw [hKB, hKBopp]
          ring
    have hTpos : 0 < H.T sign s := hH.positive sign s hspos
    apply (div_le_iff₀ hTpos).2
    calc
      H.T sign.opposite (s - 1) ≤
          Ctail * (s * Real.log (Real.exp 1 * s)) * H.T sign s := hraw
      _ ≤ C * (σ * Real.log (Real.exp 1 * σ)) * H.T sign s := by
        apply mul_le_mul_of_nonneg_right _ hTpos.le
        exact mul_le_mul (le_max_left _ _) hprodmono
          (mul_nonneg hspos.le hlogs.le) (by positivity)
  · have hsS : s ≤ S := (lt_of_not_ge htail).le
    have hlocal : proposition131iiiReverseRatio H sign s ≤ Ccompact := by
      cases sign with
      | plus =>
          calc
            proposition131iiiReverseRatio H ErrorSign.plus s ≤ Bp := hBp s ⟨hs, hsS⟩
            _ ≤ max Bp Bm := le_max_left _ _
            _ ≤ Ccompact := le_max_right _ _
      | minus =>
          calc
            proposition131iiiReverseRatio H ErrorSign.minus s ≤ Bm := hBm s ⟨hs, hsS⟩
            _ ≤ max Bp Bm := le_max_right _ _
            _ ≤ Ccompact := le_max_right _ _
    have hσfactor : 1 ≤ σ * Real.log (Real.exp 1 * σ) := by
      have hlogge : 1 ≤ Real.log (Real.exp 1 * σ) := by
        rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hσpos), Real.log_exp]
        exact le_add_of_nonneg_right (Real.log_nonneg (by linarith))
      nlinarith
    calc
      proposition131iiiReverseRatio H sign s ≤ Ccompact := hlocal
      _ ≤ Ccompact * (σ * Real.log (Real.exp 1 * σ)) := by
        exact le_mul_of_one_le_right (by dsimp [Ccompact]; positivity) hσfactor
      _ ≤ C * (σ * Real.log (Real.exp 1 * σ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
