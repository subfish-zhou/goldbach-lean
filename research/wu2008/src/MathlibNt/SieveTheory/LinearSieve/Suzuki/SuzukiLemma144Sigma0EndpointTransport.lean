import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146iErrorEnvelopeTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ExplicitRemaindersSourceOrder
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Remainder1423

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-- Claim 14.6(i) transports the direct `Σ₀` packet from its moving source
endpoint to the fixed Case-I budget coordinate. -/
theorem caseI1423_sigmaZero_realEndpoint_sourceBound
    (S : BoundingSieve) (H : Section13HatLayers)
    (C C145 K d Δ : ℝ)
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 < C) (hC145 : 0 ≤ C145) :
    ∃ A0 : ℝ, 0 ≤ A0 ∧ ∀ (N : ℕ) (s : ℝ),
      2 + (ErrorSign.ofDepth N).epsilon ≤ s →
      ∀ᶠ D : ℕ in atTop,
        s ≤ sourceSigma (D : ℝ) d →
        let σ := sourceSigma (D : ℝ) d
        let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
        caseISigmaZeroDirectRemainder S H N D C145 K d Δ ≤
          A0 * caseI1423RemainderUnit
            (sigma12InheritedBudget S H N D z C K d Δ s) (D : ℝ) σ := by
  let A0 : ℝ := C145 / C
  refine ⟨A0, div_nonneg hC145 hC.le, ?_⟩
  obtain ⟨D146, _hD146, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1
  intro N s hs
  have hs0 : 0 < s := by
    have heps : 0 ≤ (ErrorSign.ofDepth N).epsilon := by
      cases ErrorSign.ofDepth N <;> simp [ErrorSign.epsilon]
    linarith
  have hs1 : 1 ≤ s := by
    have heps : 0 ≤ (ErrorSign.ofDepth N).epsilon := by
      cases ErrorSign.ofDepth N <;> simp [ErrorSign.epsilon]
    linarith
  have hD146N : ∀ᶠ D : ℕ in atTop, D146 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D146)
  filter_upwards [hD146N, eventually_gt_atTop (3 : ℕ)] with D hlarge hD3
  intro hsσ
  dsimp only
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hD1 : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hll : 0 < Real.log (Real.log (D : ℝ)) := by
    apply Real.log_pos
    have he : Real.exp 1 < (D : ℝ) := by
      calc
        Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        _ ≤ (D : ℝ) := by exact_mod_cast (show 3 ≤ D by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity : 0 < (D : ℝ))).2 he
  have hlllog : Real.log (Real.log (D : ℝ)) ≤ Real.log (D : ℝ) := by
    have hsub := Real.log_le_sub_one_of_pos hlog
    linarith
  have hσ0 : 0 < σ := hs0.trans_le (by simpa [σ] using hsσ)
  have hpow : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) := by
    calc
      (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        exact (div_le_one hs0).2 hs1
      _ = (D : ℝ) := by norm_num
  have hzD : (z : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (Nat.ceil_le.mpr (by simpa [z] using hpow))
  have hi := (h146 (D : ℝ) hlarge).1
  have hE : errorEnvelope H N (D : ℝ) d σ ≤
      errorEnvelope H N (D : ℝ) d s := by
    apply errorEnvelope_endpoint_le_of_claim14_6
      hH.toSection13HatContract hD1 hi
    rw [hH.betaHat_eq]
    exact ⟨hs, by simpa [σ] using hsσ⟩
  have hEσ0 : 0 ≤ errorEnvelope H N (D : ℝ) d σ :=
    errorEnvelope_nonneg H N hD1 hσ0.le
      (hH.positive (ErrorSign.ofDepth N) σ hσ0).le
  have hbudget : sigma12InheritedBudget S H N D z C K d Δ σ ≤
      sigma12InheritedBudget S H N D z C K d Δ s := by
    unfold sigma12InheritedBudget
    apply mul_le_mul_of_nonneg_left hE
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC.le (Real.exp_pos _).le)
        (suzukiVProduct_pos S (z : ℝ)).le)
      (Real.rpow_nonneg hlog.le _)
  have hsrc := caseISigmaZeroDirectRemainder_le_sourceOrder
    (S := S) (H := H) (N := N) (D := D) (z := z) (K := K) (Δ := Δ)
    hD1 hll hlllog hzD (by simpa [σ] using hσ0) hC hC145
    (by simpa [σ] using hEσ0)
  calc
    caseISigmaZeroDirectRemainder S H N D C145 K d Δ ≤
        A0 * caseI1423RemainderUnit
          (sigma12InheritedBudget S H N D z C K d Δ σ) (D : ℝ) σ := by
            convert hsrc using 1;
              simp [A0, caseISourceOrderCoefficient,
                caseI1423RemainderUnit, σ]; ring
    _ ≤ A0 * caseI1423RemainderUnit
          (sigma12InheritedBudget S H N D z C K d Δ s) (D : ℝ) σ := by
      unfold caseI1423RemainderUnit
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hC145 hC.le)
      exact (div_le_div_iff_of_pos_right (mul_pos hll hσ0)).2 hbudget


end MathlibNt.SieveTheory
