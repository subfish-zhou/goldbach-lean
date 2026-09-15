import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028ReverseEnvelope

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Proposition 13.1(iii), reverse adjacent-ratio direction, with the residual
Lemma-10.28 envelope premise discharged internally from the Section-13 source
contract.  One constant works for both signs and all `2 ≤ s ≤ σ`. -/
theorem proposition131iii_uniform_reverse_adjacent_ratio_of_source
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (sign : ErrorSign) (s σ : ℝ),
      2 ≤ s → s ≤ σ →
      proposition131iiiReverseRatio H sign s ≤
        C * (σ * Real.log (Real.exp 1 * σ)) := by
  exact proposition131iii_uniform_reverse_adjacent_ratio hH
    (section13Qhat_reverseEnvelopeEdge hH)

/-- The `q_D` endpoint form used by `Σ₁₂`: the opposite-sign value at `σ-1`
is absorbed into the current error envelope with the explicit
`σ log(eσ)` loss.  For fixed `Δ ≥ 0`, the constant is uniform in the depth,
cutoff, exponent `d`, and endpoint `σ`. -/
theorem qD_opposite_le_errorEnvelope_of_source
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) (Δ : ℝ)
    (hΔ : 0 ≤ Δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (D d σ : ℝ),
      1 < D → 2 ≤ σ →
      qD H (ErrorSign.ofDepth N).opposite D d Δ σ ≤
        C * (σ * Real.log (Real.exp 1 * σ)) * errorEnvelope H N D d σ := by
  obtain ⟨A, hA, hratio⟩ :=
    proposition131iii_uniform_reverse_adjacent_ratio_of_source hH
  let C : ℝ := A * (2 : ℝ) ^ Δ
  have htwoPow : 1 ≤ (2 : ℝ) ^ Δ := by
    rw [← Real.one_rpow Δ]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num) hΔ
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro N D d σ hD hσ
  let sign := ErrorSign.ofDepth N
  have hσ0 : 0 < σ := by linarith
  have hσm0 : 0 < σ - 1 := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hpowσ : 0 ≤ σ ^ d := Real.rpow_nonneg hσ0.le _
  have hbase1 : 1 ≤ 1 + σ ^ d / Real.log D := by
    have : 0 ≤ σ ^ d / Real.log D := div_nonneg hpowσ hlogD.le
    linarith
  have hbase0 : 0 ≤ 1 + σ ^ d / Real.log D := zero_le_one.trans hbase1
  have hbasePow :
      (1 + σ ^ d / Real.log D) ^ (σ - 1) ≤
        (1 + σ ^ d / Real.log D) ^ σ := by
    exact Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
  have hfrac : σ / (σ - 1) ≤ 2 := by
    rw [div_le_iff₀ hσm0]
    linarith
  have hfrac0 : 0 ≤ σ / (σ - 1) := (div_pos hσ0 hσm0).le
  have hfracPow : (σ / (σ - 1)) ^ Δ ≤ (2 : ℝ) ^ Δ :=
    Real.rpow_le_rpow hfrac0 hfrac hΔ
  have hTcur : 0 < H.T sign σ := hH.positive sign σ hσ0
  have hTprev : 0 < H.T sign.opposite (σ - 1) :=
    hH.positive sign.opposite (σ - 1) hσm0
  have hratio' := hratio sign σ σ hσ le_rfl
  have hTshift : H.T sign.opposite (σ - 1) ≤
      A * (σ * Real.log (Real.exp 1 * σ)) * H.T sign σ := by
    apply (div_le_iff₀ hTcur).1
    simpa [proposition131iiiReverseRatio, sign] using hratio'
  have hσm_le : σ - 1 ≤ σ := by linarith
  have hlogσ : 0 < Real.log (Real.exp 1 * σ) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hσ0), Real.log_exp]
    have hlogs0 : 0 ≤ Real.log σ := Real.log_nonneg (by linarith)
    linarith
  have hcore :
      (1 + σ ^ d / Real.log D) ^ (σ - 1) * (σ - 1) *
          H.T sign.opposite (σ - 1) * (σ / (σ - 1)) ^ Δ ≤
        (A * (2 : ℝ) ^ Δ) * (σ * Real.log (Real.exp 1 * σ)) *
          ((1 + σ ^ d / Real.log D) ^ σ * σ * H.T sign σ) := by
    calc
      (1 + σ ^ d / Real.log D) ^ (σ - 1) * (σ - 1) *
            H.T sign.opposite (σ - 1) * (σ / (σ - 1)) ^ Δ ≤
          (1 + σ ^ d / Real.log D) ^ σ * σ *
            (A * (σ * Real.log (Real.exp 1 * σ)) * H.T sign σ) *
              (2 : ℝ) ^ Δ := by
        gcongr
      _ = (A * (2 : ℝ) ^ Δ) * (σ * Real.log (Real.exp 1 * σ)) *
            ((1 + σ ^ d / Real.log D) ^ σ * σ * H.T sign σ) := by ring
  simpa [qD, errorEnvelope, Section13HatLayers.kappaHat, sign, C,
    Real.rpow_one] using hcore


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
