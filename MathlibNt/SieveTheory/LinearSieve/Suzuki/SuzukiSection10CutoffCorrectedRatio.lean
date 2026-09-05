import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13BridgeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028FirstCrossing

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

open BridgeAssembly
namespace CutoffCorrectedRatio

abbrev CutoffMajorant := Section10Lemma1028FirstCrossing.Section10CommonMajorant

private lemma log_e_mul_pos {s : ℝ} (hs : 3 ≤ s) :
    0 < Real.log (Real.exp 1 * s) := by
  have hs1 : 1 ≤ s := by linarith
  have hsne : s ≠ 0 := by linarith
  rw [Real.log_mul (Real.exp_ne_zero 1) hsne, Real.log_exp]
  linarith [Real.log_nonneg hs1]

/-- Cutoff-corrected one-unit estimate for the genuine scalar `DDE(2,1,3)`.
The estimate is derived from the eventual Lemma 10.28 majorant and is not a
field of either input interface. -/
theorem section10_unitShift_after_cutoff
    {R : ℝ → ℝ} (hDDE : Section10DDEApparatus R 3)
    (Q : CutoffMajorant R) {s : ℝ} (hs : Q.cutoff ≤ s) :
    R s ≤ Q.A / (s * Real.log (Real.exp 1 * s)) * R (s - 1) := by
  have hs4 : 4 ≤ s := Q.four_le_cutoff.trans hs
  have hs0 : 0 < s := by linarith
  have hR : 0 < R s := hDDE.positive s (by linarith)
  have hA : 0 < Q.A := zero_lt_one.trans_le Q.one_le_A
  have hlog : 0 < Real.log (Real.exp 1 * s) := log_e_mul_pos (by linarith)
  have hden : 0 < s * Real.log (Real.exp 1 * s) := mul_pos hs0 hlog
  have hmaj := Q.majorizes_log s hs
  have henv := Q.envelope_slope_nonpos s hs
  have hscaled :
      s * ((1 / Q.A) * Real.log (Real.exp 1 * s)) * R s ≤ R (s - 1) := by
    have hm := mul_le_mul_of_nonneg_left hmaj hs0.le
    have hm' := mul_le_mul_of_nonneg_right hm hR.le
    nlinarith
  have hraw : s * Real.log (Real.exp 1 * s) * R s ≤ Q.A * R (s - 1) := by
    calc
      s * Real.log (Real.exp 1 * s) * R s =
          Q.A * (s * ((1 / Q.A) * Real.log (Real.exp 1 * s)) * R s) := by
            field_simp [ne_of_gt hA]
      _ ≤ Q.A * R (s - 1) := mul_le_mul_of_nonneg_left hscaled hA.le
  calc
    R s ≤ (Q.A * R (s - 1)) / (s * Real.log (Real.exp 1 * s)) := by
      apply (le_div_iff₀ hden).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw
    _ = Q.A / (s * Real.log (Real.exp 1 * s)) * R (s - 1) := by ring

/-- Sign-independent transport of the cutoff-corrected unit shift.  Both signs
use the same real `Qhat` scalar DDE domain `β = 3`. -/
theorem section13Hat_unitShift_after_cutoff
    {H : Section13HatLayers} (sign : ErrorSign)
    (B : Section13HatSection10BridgeAtThree H sign)
    (Q : CutoffMajorant B.Qhat) {s : ℝ} (hs : Q.cutoff ≤ s) :
    H.T sign s ≤
      (B.K ^ 2 * Q.A) / (s * Real.log (Real.exp 1 * s)) * H.T sign (s - 1) := by
  have hs4 : 4 ≤ s := Q.four_le_cutoff.trans hs
  have hs3 : 3 ≤ s := by linarith
  have hsm3 : 3 ≤ s - 1 := by linarith
  have hq := section10_unitShift_after_cutoff B.dde Q hs
  have hK0 : 0 ≤ B.K := zero_le_one.trans B.one_le_K
  have hcoef0 : 0 ≤ Q.A / (s * Real.log (Real.exp 1 * s)) :=
    div_nonneg (zero_le_one.trans Q.one_le_A)
      (mul_nonneg (by linarith) (log_e_mul_pos hs3).le)
  calc
    H.T sign s ≤ B.K * B.Qhat s := B.hat_le s hs3
    _ ≤ B.K * (Q.A / (s * Real.log (Real.exp 1 * s)) * B.Qhat (s - 1)) :=
      mul_le_mul_of_nonneg_left hq hK0
    _ ≤ B.K * (Q.A / (s * Real.log (Real.exp 1 * s)) *
        (B.K * H.T sign (s - 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (B.Q_le (s - 1) hsm3) hcoef0) hK0
    _ = (B.K ^ 2 * Q.A) / (s * Real.log (Real.exp 1 * s)) *
        H.T sign (s - 1) := by ring

/-- The corresponding two-unit ratio, obtained by two applications of the
cutoff-corrected unit shift (and not stored in either source record). -/
theorem section13Hat_twoStep_after_cutoff
    {H : Section13HatLayers} (sign : ErrorSign)
    (B : Section13HatSection10BridgeAtThree H sign)
    (Q : CutoffMajorant B.Qhat) {M : ℝ} (hM : Q.cutoff ≤ M + 1) :
    H.T sign (M + 2) ≤
      (B.K ^ 2 * Q.A) ^ 2 /
        (((M + 1) * Real.log (Real.exp 1 * (M + 1))) *
          ((M + 2) * Real.log (Real.exp 1 * (M + 2)))) * H.T sign M := by
  have hM4 : 4 ≤ M + 1 := Q.four_le_cutoff.trans hM
  have h1 := section13Hat_unitShift_after_cutoff sign B Q hM
  have h2 := section13Hat_unitShift_after_cutoff sign B Q
    (hM.trans (by linarith : M + 1 ≤ M + 2))
  have hd1 : 0 < (M + 1) * Real.log (Real.exp 1 * (M + 1)) :=
    mul_pos (by linarith) (log_e_mul_pos (by linarith))
  have hd2 : 0 < (M + 2) * Real.log (Real.exp 1 * (M + 2)) :=
    mul_pos (by linarith) (log_e_mul_pos (by linarith))
  have hc2 : 0 ≤ (B.K ^ 2 * Q.A) /
      ((M + 2) * Real.log (Real.exp 1 * (M + 2))) := by
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (zero_le_one.trans Q.one_le_A)) hd2.le
  have hchain : H.T sign (M + 2) ≤
      ((B.K ^ 2 * Q.A) / ((M + 2) * Real.log (Real.exp 1 * (M + 2)))) *
        (((B.K ^ 2 * Q.A) / ((M + 1) * Real.log (Real.exp 1 * (M + 1)))) *
          H.T sign M) := by
    calc
      H.T sign (M + 2) ≤
          ((B.K ^ 2 * Q.A) / ((M + 2) * Real.log (Real.exp 1 * (M + 2)))) *
            H.T sign (M + 1) := by
        convert h2 using 1
        ring_nf
      _ ≤ ((B.K ^ 2 * Q.A) / ((M + 2) * Real.log (Real.exp 1 * (M + 2)))) *
          (((B.K ^ 2 * Q.A) / ((M + 1) * Real.log (Real.exp 1 * (M + 1)))) *
            H.T sign M) := by
        apply mul_le_mul_of_nonneg_left _ hc2
        simpa only [add_sub_cancel_right] using h1
  calc
    H.T sign (M + 2) ≤ _ := hchain
    _ = (B.K ^ 2 * Q.A) ^ 2 /
        (((M + 1) * Real.log (Real.exp 1 * (M + 1))) *
          ((M + 2) * Real.log (Real.exp 1 * (M + 2)))) * H.T sign M := by
      field_simp [ne_of_gt hd1, ne_of_gt hd2]

private noncomputable def compactRatio
    (H : Section13HatLayers) (sign : ErrorSign) (M : ℝ) : ℝ :=
  weightedHat H sign (M + 2) *
      (M * Real.log (Real.exp 1 * M)) ^ 2 / weightedHat H sign M

private lemma compactRatio_continuousOn
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) (S : ℝ) :
    ContinuousOn (compactRatio H sign) (Icc 3 S) := by
  have hT : ContinuousOn (H.T sign) (Ioi 0) := hH.continuous sign
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx20 : 0 < x + 2 := by linarith [hx.1]
  have hTx : ContinuousAt (H.T sign) x :=
    hT.continuousAt (Ioi_mem_nhds hx0)
  have hTx2 : ContinuousAt (H.T sign) (x + 2) :=
    hT.continuousAt (Ioi_mem_nhds hx20)
  have hshift : ContinuousAt (fun y : ℝ => H.T sign (y + 2)) x :=
    hTx2.comp_of_eq (continuousAt_id.add continuousAt_const) rfl
  have harg : ContinuousAt (fun y : ℝ => Real.exp 1 * y) x :=
    continuousAt_const.mul continuousAt_id
  have hlog : ContinuousAt (fun y : ℝ => Real.log (Real.exp 1 * y)) x :=
    harg.log (mul_ne_zero (Real.exp_ne_zero 1) (ne_of_gt hx0))
  have hw0 : ContinuousAt (weightedHat H sign) x := by
    change ContinuousAt (fun y : ℝ => y ^ 2 * H.T sign y) x
    exact (continuousAt_id.pow 2).mul hTx
  have hw2 : ContinuousAt (fun y : ℝ => weightedHat H sign (y + 2)) x := by
    change ContinuousAt (fun y : ℝ => (y + 2) ^ 2 * H.T sign (y + 2)) x
    exact ((continuousAt_id.add continuousAt_const).pow 2).mul hshift
  have hden : weightedHat H sign x ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hx0))
      (ne_of_gt (hH.positive sign x hx0))
  exact ((hw2.mul ((continuousAt_id.mul hlog).pow 2)).div hw0 hden).continuousWithinAt

private theorem compactRatio_bound
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) (S : ℝ) :
    ∃ B : ℝ, ∀ M, M ∈ Icc (3 : ℝ) S → compactRatio H sign M ≤ B := by
  have hb := isCompact_Icc.bddAbove_image (compactRatio_continuousOn hH sign S)
  rw [bddAbove_def] at hb
  obtain ⟨B, hB⟩ := hb
  refine ⟨B, ?_⟩
  intro M hM
  exact hB _ ⟨M, hM, rfl⟩

/-- Cutoff-corrected Proposition 13.1 ratio interface.  The compact interval
before the eventual cutoff is handled only by continuity and positivity; after
the cutoff, two derived unit shifts provide the logarithmic-square decay. -/
theorem section13HatAsymptoticContract_of_atThree_cutoff
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (bridge : ∀ sign, Section13HatSection10BridgeAtThree H sign)
    (majorant : ∀ sign, CutoffMajorant (bridge sign).Qhat) :
    Section13HatAsymptoticContract H := by
  let bp := bridge ErrorSign.plus
  let bm := bridge ErrorSign.minus
  let qp := majorant ErrorSign.plus
  let qm := majorant ErrorSign.minus
  let S : ℝ := max qp.cutoff qm.cutoff
  have hS4 : 4 ≤ S := qp.four_le_cutoff.trans (le_max_left _ _)
  obtain ⟨Bp, hBp⟩ := compactRatio_bound hH ErrorSign.plus S
  obtain ⟨Bm, hBm⟩ := compactRatio_bound hH ErrorSign.minus S
  let Ap : ℝ := bp.K ^ 2 * qp.A
  let Am : ℝ := bm.K ^ 2 * qm.A
  let A : ℝ := max Ap Am
  let Ctail : ℝ := 3 * A ^ 2
  let Ccompact : ℝ := max 1 (max Bp Bm)
  let C : ℝ := max Ctail Ccompact
  have hAp1 : 1 ≤ Ap := by dsimp [Ap]; nlinarith [bp.one_le_K, qp.one_le_A]
  have hA1 : 1 ≤ A := hAp1.trans (le_max_left _ _)
  have hCtail0 : 0 < Ctail := by dsimp [Ctail]; positivity
  have hCpos : 0 < C := hCtail0.trans_le (le_max_left _ _)
  refine ⟨C, hCpos.le, ?_⟩
  intro sign M hM
  have hM0 : 0 < M := by linarith
  have hL : 0 < Real.log (Real.exp 1 * M) := log_e_mul_pos (by linarith)
  have hd0 : 0 < M * Real.log (Real.exp 1 * M) := mul_pos hM0 hL
  have hTM0 : 0 < H.T sign M := hH.positive sign M hM0
  have hW0 : 0 < weightedHat H sign M :=
    mul_pos (sq_pos_of_pos hM0) hTM0
  by_cases htail : S ≤ M + 1
  · let B := bridge sign
    let Q := majorant sign
    let E : ℝ := B.K ^ 2 * Q.A
    have hQS : Q.cutoff ≤ S := by
      cases sign with
      | plus => exact le_max_left _ _
      | minus => exact le_max_right _ _
    have hcut1 : Q.cutoff ≤ M + 1 := hQS.trans htail
    have hcut2 : Q.cutoff ≤ M + 2 := hcut1.trans (by linarith)
    have hEA : E ≤ A := by
      cases sign with
      | plus => exact le_max_left _ _
      | minus => exact le_max_right _ _
    have hE0 : 0 ≤ E := mul_nonneg (sq_nonneg _) (zero_le_one.trans Q.one_le_A)
    have h1 := section13Hat_unitShift_after_cutoff sign B Q hcut1
    have h2 := section13Hat_unitShift_after_cutoff sign B Q hcut2
    have hTM1 : 0 ≤ H.T sign (M + 1) := (hH.positive sign (M + 1) (by linarith)).le
    have hlog1 : Real.log (Real.exp 1 * M) ≤ Real.log (Real.exp 1 * (M + 1)) :=
      Real.log_le_log (by positivity) (by gcongr; linarith)
    have hlog2 : Real.log (Real.exp 1 * M) ≤ Real.log (Real.exp 1 * (M + 2)) :=
      Real.log_le_log (by positivity) (by gcongr; linarith)
    have hd1 : M * Real.log (Real.exp 1 * M) ≤
        (M + 1) * Real.log (Real.exp 1 * (M + 1)) :=
      mul_le_mul (by linarith) hlog1 hL.le (by linarith)
    have hd2 : M * Real.log (Real.exp 1 * M) ≤
        (M + 2) * Real.log (Real.exp 1 * (M + 2)) :=
      mul_le_mul (by linarith) hlog2 hL.le (by linarith)
    have hc1 : E / ((M + 1) * Real.log (Real.exp 1 * (M + 1))) ≤ A / (M * Real.log (Real.exp 1 * M)) := by
      calc
        _ ≤ E / (M * Real.log (Real.exp 1 * M)) := div_le_div_of_nonneg_left hE0 hd0 hd1
        _ ≤ _ := div_le_div_of_nonneg_right hEA hd0.le
    have hc2 : E / ((M + 2) * Real.log (Real.exp 1 * (M + 2))) ≤ A / (M * Real.log (Real.exp 1 * M)) := by
      calc
        _ ≤ E / (M * Real.log (Real.exp 1 * M)) := div_le_div_of_nonneg_left hE0 hd0 hd2
        _ ≤ _ := div_le_div_of_nonneg_right hEA hd0.le
    have hc0 : 0 ≤ A / (M * Real.log (Real.exp 1 * M)) :=
      div_nonneg (zero_le_one.trans hA1) hd0.le
    have h1Q : H.T sign (M + 1) ≤
        E / ((M + 1) * Real.log (Real.exp 1 * (M + 1))) * H.T sign M := by
      change H.T sign (M + 1) ≤
        (B.K ^ 2 * Q.A) / ((M + 1) * Real.log (Real.exp 1 * (M + 1))) * H.T sign M
      convert h1 using 1 <;> ring_nf
    have h2Q : H.T sign (M + 2) ≤
        E / ((M + 2) * Real.log (Real.exp 1 * (M + 2))) * H.T sign (M + 1) := by
      change H.T sign (M + 2) ≤
        (B.K ^ 2 * Q.A) / ((M + 2) * Real.log (Real.exp 1 * (M + 2))) * H.T sign (M + 1)
      convert h2 using 1 <;> ring_nf
    have h1' : H.T sign (M + 1) ≤ (A / (M * Real.log (Real.exp 1 * M))) * H.T sign M := by
      exact h1Q.trans (mul_le_mul_of_nonneg_right hc1 hTM0.le)
    have h2' : H.T sign (M + 2) ≤ (A / (M * Real.log (Real.exp 1 * M))) * H.T sign (M + 1) := by
      exact h2Q.trans (mul_le_mul_of_nonneg_right hc2 hTM1)
    have hchain : H.T sign (M + 2) ≤
        (A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M := by
      calc
        _ ≤ (A / (M * Real.log (Real.exp 1 * M))) * H.T sign (M + 1) := h2'
        _ ≤ (A / (M * Real.log (Real.exp 1 * M))) *
            ((A / (M * Real.log (Real.exp 1 * M))) * H.T sign M) :=
          mul_le_mul_of_nonneg_left h1' hc0
        _ = _ := by ring
    have hratio : (M + 2) ^ 2 ≤ 3 * M ^ 2 := by nlinarith
    have hweighted := mul_le_mul_of_nonneg_left hchain (sq_nonneg (M + 2))
    have htailfinal : weightedHat H sign (M + 2) ≤
        (Ctail / (M * Real.log (Real.exp 1 * M)) ^ 2) * weightedHat H sign M := by
      calc
        weightedHat H sign (M + 2) ≤ (M + 2) ^ 2 *
            ((A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M) := by
          simpa only [weightedHat] using hweighted
        _ ≤ (3 * M ^ 2) * ((A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M) :=
          mul_le_mul_of_nonneg_right hratio (mul_nonneg (sq_nonneg _) hTM0.le)
        _ = (Ctail / (M * Real.log (Real.exp 1 * M)) ^ 2) * weightedHat H sign M := by
          dsimp [Ctail, weightedHat]
          field_simp [ne_of_gt hM0, ne_of_gt hL]
    exact htailfinal.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hW0.le)
  · have hMS : M ≤ S := by linarith
    have hlocal : compactRatio H sign M ≤ Ccompact := by
      cases sign with
      | plus => exact (hBp M ⟨by linarith, hMS⟩).trans ((le_max_left Bp Bm).trans (le_max_right 1 _))
      | minus => exact (hBm M ⟨by linarith, hMS⟩).trans ((le_max_right Bp Bm).trans (le_max_right 1 _))
    have hlocalC : compactRatio H sign M ≤ C := hlocal.trans (le_max_right _ _)
    change weightedHat H sign (M + 2) ≤
      (C / (M * Real.log (Real.exp 1 * M)) ^ 2) * weightedHat H sign M
    dsimp [compactRatio] at hlocalC
    have hmul : weightedHat H sign (M + 2) *
        (M * Real.log (Real.exp 1 * M)) ^ 2 ≤ C * weightedHat H sign M :=
      (div_le_iff₀ hW0).1 hlocalC
    calc
      weightedHat H sign (M + 2) =
          (weightedHat H sign (M + 2) * (M * Real.log (Real.exp 1 * M)) ^ 2) /
            (M * Real.log (Real.exp 1 * M)) ^ 2 := by
              apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hd0))).2
              ring
      _ ≤ (C * weightedHat H sign M) / (M * Real.log (Real.exp 1 * M)) ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hd0)).2 hmul
      _ = (C / (M * Real.log (Real.exp 1 * M)) ^ 2) * weightedHat H sign M := by ring


end CutoffCorrectedRatio
end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
