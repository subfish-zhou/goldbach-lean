import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131TailDecay

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-!
# Section 10 DDE reduction for the Proposition 13.1 unit shift

This file deliberately stops the source boundary *before* Lemma 10.29.  The
remaining source input is the one-sided conclusion of Lemma 10.28: the
logarithmic slope of the decreasing common-majorant envelope is non-positive.
The unit-shift estimate and its two-step Section 13 consumer are proved below.
-/

/-- The Iwaniec pairing in §10, specialized to the coefficient `b = 1`. -/
noncomputable def section10Pairing
    (R r : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * r s * R s - ∫ t in s - 1..s, r (t + 1) * R t

/-- Minimal non-circular `DDE(2,1,β)` apparatus used at `κ = 1`.

The record contains the original and adjoint equations, positivity, and the
vanishing pairing.  It contains no adjacent-value estimate. -/
structure Section10DDEApparatus (R : ℝ → ℝ) (β : ℝ) where
  adjoint : ℝ → ℝ
  beta_ge_one : 1 ≤ β
  continuous : ContinuousOn R (Ioi (β - 1))
  positive : ∀ s, β - 1 < s → 0 < R s
  adjoint_positive : ∀ s, β ≤ s → 0 < adjoint s
  original_dde : ∀ s, β < s →
    HasDerivAt R (-(2 * R s + R (s - 1)) / s) s
  adjoint_dde : ∀ s, 0 < s →
    HasDerivAt (fun u => u * adjoint u)
      (2 * adjoint s + adjoint (s + 1)) s
  pairing_zero : ∀ s, β < s → section10Pairing R adjoint s = 0

/-- The common majorant `ξ` and the decreasing envelope furnished by the
one-sided half of source Lemma 10.28.  The displayed `envelope_slope_nonpos`
is equation (10.44) after multiplying by the positive quantity `s R(s)`;
`majorizes_log` is the elementary Proposition 10.20 comparison, with bounded
initial values absorbed into `A`.

This is strictly upstream of Lemma 10.29: no statement comparing `R(s-1)` and
`R(s)` is a field of this record. -/
structure Section10CommonMajorant (R : ℝ → ℝ) where
  xi : ℝ → ℝ
  cMinus : ℝ
  A : ℝ
  one_le_A : 1 ≤ A
  majorizes_log : ∀ s, 3 ≤ s →
    (1 / A) * Real.log (Real.exp 1 * s) ≤ xi s - cMinus - 2 / s
  envelope_slope_nonpos : ∀ s, 3 ≤ s →
    -(R (s - 1)) + s * (xi s - cMinus - 2 / s) * R s ≤ 0

/- Lemma 10.28 is the explicit source boundary of this reduction.  Callers
must supply an actual `Section10CommonMajorant`; it is not postulated here. -/

/-- Lemma 10.17 and the Proposition 13.1 construction: `Q̂` satisfies the
positive `DDE(2,1,β)` apparatus and is uniformly comparable with each `T̂±`.
No adjacent-value estimate is included. -/
structure Section13HatSection10Bridge
    (H : Section13HatLayers) (sign : ErrorSign) where
  Qhat : ℝ → ℝ
  dde : Section10DDEApparatus Qhat (2 + sign.epsilon)
  K : ℝ
  one_le_K : 1 ≤ K
  hat_le : ∀ s, 2 + sign.epsilon ≤ s → H.T sign s ≤ K * Qhat s
  Q_le : ∀ s, 2 + sign.epsilon ≤ s → Qhat s ≤ K * H.T sign s

/- Equations (13.8)--(13.10) and Lemma 10.17 form the other explicit source
boundary.  Callers must supply an actual bridge for each sign. -/

private lemma log_e_mul_pos {s : ℝ} (hs : 3 ≤ s) :
    0 < Real.log (Real.exp 1 * s) := by
  have hs1 : 1 ≤ s := by linarith
  have hsne : s ≠ 0 := by linarith
  rw [Real.log_mul (Real.exp_ne_zero 1) hsne, Real.log_exp]
  linarith [Real.log_nonneg hs1]

/-- The one-sided `κ=1` content of Lemma 10.29, now derived from the
Lemma-10.28 common envelope rather than postulated as a ratio field. -/
theorem section10_lemma1029_unitShift_one_sided
    {R : ℝ → ℝ} {β s : ℝ} (hDDE : Section10DDEApparatus R β)
    (Q : Section10CommonMajorant R) (hβ : β ≤ 3) (hs : 3 ≤ s) :
    s * Real.log (Real.exp 1 * s) * R s ≤
      Q.A * R (s - 1) := by
  have hA : 0 < Q.A := zero_lt_one.trans_le Q.one_le_A
  have hs0 : 0 < s := by linarith
  have hR : 0 < R s := hDDE.positive s (by linarith)
  have hmaj := Q.majorizes_log s hs
  have henv := Q.envelope_slope_nonpos s hs
  have hscaled :
      s * ((1 / Q.A) * Real.log (Real.exp 1 * s)) * R s ≤ R (s - 1) := by
    have hm := mul_le_mul_of_nonneg_left hmaj hs0.le
    have hm' := mul_le_mul_of_nonneg_right hm hR.le
    nlinarith
  calc
    s * Real.log (Real.exp 1 * s) * R s =
        Q.A * (s * ((1 / Q.A) * Real.log (Real.exp 1 * s)) * R s) := by
          field_simp [ne_of_gt hA]
    _ ≤ Q.A * R (s - 1) := mul_le_mul_of_nonneg_left hscaled hA.le

/-- Division form of the one-step bound used twice in Proposition 13.1. -/
theorem section10_unitShift_forward
    {R : ℝ → ℝ} {β s : ℝ} (hDDE : Section10DDEApparatus R β)
    (Q : Section10CommonMajorant R) (hβ : β ≤ 3) (hs : 3 ≤ s) :
    R s ≤ Q.A /
      (s * Real.log (Real.exp 1 * s)) * R (s - 1) := by
  have hs0 : 0 < s := by linarith
  have hlog : 0 < Real.log (Real.exp 1 * s) := log_e_mul_pos hs
  have hden : 0 < s * Real.log (Real.exp 1 * s) := mul_pos hs0 hlog
  have h := section10_lemma1029_unitShift_one_sided hDDE Q hβ hs
  calc
    R s ≤ (Q.A * R (s - 1)) /
        (s * Real.log (Real.exp 1 * s)) := by
      apply (le_div_iff₀ hden).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    _ = Q.A / (s * Real.log (Real.exp 1 * s)) * R (s - 1) := by ring

/-- Lemma 10.17 transports Lemma 10.29 from the common majorant `Q̂` to
one hat layer. -/
theorem section13Hat_unitShift_forward
    {H : Section13HatLayers} (sign : ErrorSign)
    (B : Section13HatSection10Bridge H sign)
    (Q : Section10CommonMajorant B.Qhat) {s : ℝ} (hs : 4 ≤ s) :
    H.T sign s ≤
      (B.K ^ 2 * Q.A) /
        (s * Real.log (Real.exp 1 * s)) * H.T sign (s - 1) := by
  have hβ : 2 + sign.epsilon ≤ 3 := by
    cases sign <;> norm_num [ErrorSign.epsilon]
  have hsβ : 2 + sign.epsilon ≤ s := hβ.trans (by linarith)
  have hsmβ : 2 + sign.epsilon ≤ s - 1 := by
    cases sign <;> norm_num [ErrorSign.epsilon] <;> linarith
  have hq := section10_unitShift_forward (s := s) B.dde Q hβ (by linarith)
  have hK0 : 0 ≤ B.K := zero_le_one.trans B.one_le_K
  have hcoef0 : 0 ≤ Q.A / (s * Real.log (Real.exp 1 * s)) :=
    div_nonneg (zero_le_one.trans Q.one_le_A)
      (mul_nonneg (by linarith) (log_e_mul_pos (by linarith)).le)
  calc
    H.T sign s ≤ B.K * B.Qhat s := B.hat_le s hsβ
    _ ≤ B.K * (Q.A / (s * Real.log (Real.exp 1 * s)) * B.Qhat (s - 1)) :=
      mul_le_mul_of_nonneg_left hq hK0
    _ ≤ B.K * (Q.A / (s * Real.log (Real.exp 1 * s)) *
        (B.K * H.T sign (s - 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (B.Q_le (s - 1) hsmβ) hcoef0) hK0
    _ = (B.K ^ 2 * Q.A) / (s * Real.log (Real.exp 1 * s)) *
        H.T sign (s - 1) := by ring

/-- Internalized Proposition 13.1(iii) contract.  Two one-unit applications of
Lemma 10.29 give the required two-unit weighted ratio; elementary monotonicity
of `s` and `log(es)` supplies a single uniform constant for both signs. -/
theorem section13HatAsymptoticContract_of_section10
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (bridge : ∀ sign, Section13HatSection10Bridge H sign)
    (majorant : ∀ sign, Section10CommonMajorant (bridge sign).Qhat) :
    Section13HatAsymptoticContract H := by
  let bp := bridge ErrorSign.plus
  let bm := bridge ErrorSign.minus
  let qp := majorant ErrorSign.plus
  let qm := majorant ErrorSign.minus
  let Ap : ℝ := bp.K ^ 2 * qp.A
  let Am : ℝ := bm.K ^ 2 * qm.A
  let A : ℝ := max Ap Am
  let C : ℝ := 3 * A ^ 2
  have hAp1 : 1 ≤ Ap := by
    dsimp [Ap]
    nlinarith [bp.one_le_K, qp.one_le_A]
  have hA1 : 1 ≤ A := hAp1.trans (le_max_left _ _)
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro sign M hM
  let B := bridge sign
  let Q := majorant sign
  let E : ℝ := B.K ^ 2 * Q.A
  have hEA : E ≤ A := by
    cases sign with
    | plus => exact le_max_left _ _
    | minus => exact le_max_right _ _
  have hE0 : 0 ≤ E := mul_nonneg (sq_nonneg _) (zero_le_one.trans Q.one_le_A)
  have hM0 : 0 < M := by linarith
  have h1 := section13Hat_unitShift_forward sign B Q (by linarith : 4 ≤ M + 1)
  have h2 := section13Hat_unitShift_forward sign B Q (by linarith : 4 ≤ M + 2)
  have h1Q : H.T sign (M + 1) ≤
      E / ((M + 1) * Real.log (Real.exp 1 * (M + 1))) * H.T sign M := by
    change H.T sign (M + 1) ≤
      (B.K ^ 2 * Q.A) / ((M + 1) * Real.log (Real.exp 1 * (M + 1))) * H.T sign M
    convert h1 using 1
    all_goals ring_nf
  have h2Q : H.T sign (M + 2) ≤
      E / ((M + 2) * Real.log (Real.exp 1 * (M + 2))) * H.T sign (M + 1) := by
    change H.T sign (M + 2) ≤
      (B.K ^ 2 * Q.A) / ((M + 2) * Real.log (Real.exp 1 * (M + 2))) *
        H.T sign (M + 1)
    convert h2 using 1
    all_goals ring_nf
  have hTM0 : 0 ≤ H.T sign M := (hH.positive sign M hM0).le
  have hTM1 : 0 ≤ H.T sign (M + 1) :=
    (hH.positive sign (M + 1) (by linarith)).le
  have hL : 0 < Real.log (Real.exp 1 * M) := log_e_mul_pos (by linarith)
  have hlog1 : Real.log (Real.exp 1 * M) ≤
      Real.log (Real.exp 1 * (M + 1)) := by
    exact Real.log_le_log (by positivity) (by gcongr; linarith)
  have hlog2 : Real.log (Real.exp 1 * M) ≤
      Real.log (Real.exp 1 * (M + 2)) := by
    exact Real.log_le_log (by positivity) (by gcongr; linarith)
  have hd1 : M * Real.log (Real.exp 1 * M) ≤
      (M + 1) * Real.log (Real.exp 1 * (M + 1)) :=
    mul_le_mul (by linarith) hlog1 hL.le (by linarith)
  have hd2 : M * Real.log (Real.exp 1 * M) ≤
      (M + 2) * Real.log (Real.exp 1 * (M + 2)) :=
    mul_le_mul (by linarith) hlog2 hL.le (by linarith)
  have hd0 : 0 < M * Real.log (Real.exp 1 * M) := mul_pos hM0 hL
  have hc1 : E / ((M + 1) * Real.log (Real.exp 1 * (M + 1))) ≤
      A / (M * Real.log (Real.exp 1 * M)) := by
    calc
      E / ((M + 1) * Real.log (Real.exp 1 * (M + 1))) ≤
          E / (M * Real.log (Real.exp 1 * M)) :=
        div_le_div_of_nonneg_left hE0 hd0 hd1
      _ ≤ A / (M * Real.log (Real.exp 1 * M)) :=
        div_le_div_of_nonneg_right hEA hd0.le
  have hc2 : E / ((M + 2) * Real.log (Real.exp 1 * (M + 2))) ≤
      A / (M * Real.log (Real.exp 1 * M)) := by
    calc
      E / ((M + 2) * Real.log (Real.exp 1 * (M + 2))) ≤
          E / (M * Real.log (Real.exp 1 * M)) :=
        div_le_div_of_nonneg_left hE0 hd0 hd2
      _ ≤ A / (M * Real.log (Real.exp 1 * M)) :=
        div_le_div_of_nonneg_right hEA hd0.le
  have hc0 : 0 ≤ A / (M * Real.log (Real.exp 1 * M)) := div_nonneg hA0 hd0.le
  have h1' : H.T sign (M + 1) ≤
      (A / (M * Real.log (Real.exp 1 * M))) * H.T sign M :=
    h1Q.trans (mul_le_mul_of_nonneg_right hc1 hTM0)
  have h2' : H.T sign (M + 2) ≤
      (A / (M * Real.log (Real.exp 1 * M))) * H.T sign (M + 1) :=
    h2Q.trans (mul_le_mul_of_nonneg_right hc2 hTM1)
  have hchain : H.T sign (M + 2) ≤
      (A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M := by
    calc
      H.T sign (M + 2) ≤
          (A / (M * Real.log (Real.exp 1 * M))) * H.T sign (M + 1) := h2'
      _ ≤ (A / (M * Real.log (Real.exp 1 * M))) *
          ((A / (M * Real.log (Real.exp 1 * M))) * H.T sign M) :=
        mul_le_mul_of_nonneg_left h1' hc0
      _ = (A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M := by ring
  have hratio : (M + 2) ^ 2 ≤ 3 * M ^ 2 := by nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hchain (sq_nonneg (M + 2))
  calc
    weightedHat H sign (M + 2) ≤
        (M + 2) ^ 2 *
          ((A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M) := by
      simpa only [weightedHat] using hweighted
    _ ≤ (3 * M ^ 2) *
          ((A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg (sq_nonneg _) hTM0)
    _ = (C / (M * Real.log (Real.exp 1 * M)) ^ 2) *
          weightedHat H sign M := by
      dsimp [C, weightedHat]
      field_simp [ne_of_gt hM0, ne_of_gt hL]


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
