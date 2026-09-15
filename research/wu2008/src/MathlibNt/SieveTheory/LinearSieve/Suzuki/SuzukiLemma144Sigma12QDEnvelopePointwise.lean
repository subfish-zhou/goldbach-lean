import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131TailDecay

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-!
# The `Σ₁₂` endpoint `q_D` factor

The literal factor-one predicate in
`CaseISigma12QDEnvelopeFactor` is false for arbitrary `Section13HatLayers`:
its structure carries no relation between the two signed layers.  The endpoint
argument only needs a factor fixed in `D`.  The result below supplies exactly
that factor from the positive Section-13 contract; in particular the desired
comparison is not assumed as a premise.
-/

/-- The fixed-in-`D` signed-layer quotient occurring after `qD` and
`errorEnvelope` are expanded. -/
noncomputable def caseISigma12QDFixedFactor
    (H : Section13HatLayers) (N : ℕ) (Δ s : ℝ) : ℝ :=
  (s / (s - 1)) ^ Δ *
    (H.T (ErrorSign.ofDepth N).opposite (s - 1) /
      H.T (ErrorSign.ofDepth N) s)

/-- At successor depth, the delayed layer in `q_D^∓` is literally the layer
selected by the predecessor parity. -/
theorem caseISigma12_qD_sign_eq_pred
    (H : Section13HatLayers) {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    H.T (ErrorSign.ofDepth N).opposite (s - 1) =
      H.T (ErrorSign.ofDepth (N - 1)) (s - 1) := by
  rw [ErrorSign.ofDepth_pred_eq_opposite hN]

/-- The endpoint value `q_D^∓(s)` is bounded by a factor independent of `D`
times the inherited envelope.  This is the source-order comparison required by
`Σ₁₂`; the fixed factor can subsequently be absorbed by the existing strict
source-order gap. -/
theorem caseISigma12_qD_le_fixedFactor_mul_errorEnvelope
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (N : ℕ) {D d Δ s : ℝ} (hD : 1 < D) (hs : 2 ≤ s) :
    qD H (ErrorSign.ofDepth N).opposite D d Δ s ≤
      caseISigma12QDFixedFactor H N Δ s * errorEnvelope H N D d s := by
  let sign := ErrorSign.ofDepth N
  have hs0 : 0 < s := by linarith
  have hsm0 : 0 < s - 1 := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hbase : 1 ≤ 1 + s ^ d / Real.log D := by
    have hz : 0 ≤ s ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg hs0.le _) hlog.le
    linarith
  have hbase0 : 0 ≤ 1 + s ^ d / Real.log D := zero_le_one.trans hbase
  have hpow :
      (1 + s ^ d / Real.log D) ^ (s - 1) ≤
        (1 + s ^ d / Real.log D) ^ s := by
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hTcur : 0 < H.T sign s := hH.positive sign s hs0
  have hTcur_ne : H.T (ErrorSign.ofDepth N) s ≠ 0 := by
    simpa [sign] using hTcur.ne'
  have hTdelay : 0 ≤ H.T sign.opposite (s - 1) :=
    (hH.positive sign.opposite (s - 1) hsm0).le
  have hratio : 0 ≤ (s / (s - 1)) ^ Δ :=
    Real.rpow_nonneg (div_nonneg hs0.le hsm0.le) _
  have hcore :
      (1 + s ^ d / Real.log D) ^ (s - 1) * (s - 1) ≤
        (1 + s ^ d / Real.log D) ^ s * s := by
    calc
      (1 + s ^ d / Real.log D) ^ (s - 1) * (s - 1) ≤
          (1 + s ^ d / Real.log D) ^ s * (s - 1) :=
        mul_le_mul_of_nonneg_right hpow hsm0.le
      _ ≤ (1 + s ^ d / Real.log D) ^ s * s :=
        mul_le_mul_of_nonneg_left (by linarith)
          (Real.rpow_nonneg hbase0 s)
  unfold qD errorEnvelope Section13HatLayers.kappaHat
  dsimp [caseISigma12QDFixedFactor, sign]
  norm_num [Real.rpow_one]
  have hscaled := mul_le_mul_of_nonneg_right hcore (mul_nonneg hTdelay hratio)
  calc
    (1 + s ^ d / Real.log D) ^ (s - 1) * (s - 1) *
          H.T (ErrorSign.ofDepth N).opposite (s - 1) *
          (s / (s - 1)) ^ Δ =
        ((1 + s ^ d / Real.log D) ^ (s - 1) * (s - 1)) *
          (H.T (ErrorSign.ofDepth N).opposite (s - 1) *
            (s / (s - 1)) ^ Δ) := by ring
    _ ≤ ((1 + s ^ d / Real.log D) ^ s * s) *
          (H.T (ErrorSign.ofDepth N).opposite (s - 1) *
            (s / (s - 1)) ^ Δ) := hscaled
    _ = ((s / (s - 1)) ^ Δ *
          (H.T (ErrorSign.ofDepth N).opposite (s - 1) /
            H.T (ErrorSign.ofDepth N) s)) *
          ((1 + s ^ d / Real.log D) ^ s * s *
            H.T (ErrorSign.ofDepth N) s) := by
      have hcancel :
          (H.T (ErrorSign.ofDepth N).opposite (s - 1) /
              H.T (ErrorSign.ofDepth N) s) *
            H.T (ErrorSign.ofDepth N) s =
          H.T (ErrorSign.ofDepth N).opposite (s - 1) :=
        div_mul_cancel₀ _ hTcur_ne
      rw [show ((s / (s - 1)) ^ Δ *
              (H.T (ErrorSign.ofDepth N).opposite (s - 1) /
                H.T (ErrorSign.ofDepth N) s)) *
            ((1 + s ^ d / Real.log D) ^ s * s *
              H.T (ErrorSign.ofDepth N) s) =
          ((1 + s ^ d / Real.log D) ^ s * s * (s / (s - 1)) ^ Δ) *
            ((H.T (ErrorSign.ofDepth N).opposite (s - 1) /
                H.T (ErrorSign.ofDepth N) s) *
              H.T (ErrorSign.ofDepth N) s) by ring, hcancel]
      ring

/-- Packaged form: for fixed `H,N,Δ,s`, one nonnegative constant works for every
`D>1` and every `d`. -/
theorem exists_caseISigma12_qD_envelope_factor
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (N : ℕ) {Δ s : ℝ} (hs : 2 ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ D d : ℝ, 1 < D →
      qD H (ErrorSign.ofDepth N).opposite D d Δ s ≤
        A * errorEnvelope H N D d s := by
  refine ⟨caseISigma12QDFixedFactor H N Δ s, ?_, ?_⟩
  · dsimp [caseISigma12QDFixedFactor]
    have hs0 : 0 < s := by linarith
    have hsm0 : 0 < s - 1 := by linarith
    exact mul_nonneg
      (Real.rpow_nonneg (div_nonneg hs0.le hsm0.le) _)
      (div_nonneg
        (hH.positive (ErrorSign.ofDepth N).opposite (s - 1) hsm0).le
        (hH.positive (ErrorSign.ofDepth N) s hs0).le)
  · intro D d hD
    exact caseISigma12_qD_le_fixedFactor_mul_errorEnvelope hH N hD hs


end MathlibNt.SieveTheory
