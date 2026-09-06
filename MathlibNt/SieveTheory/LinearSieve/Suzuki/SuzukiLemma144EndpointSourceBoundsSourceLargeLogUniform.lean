import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132SlackFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiiReverseFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseI1423SigmaCubedDecay
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12QDEnvelopePointwise
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ExplicitRemaindersSourceOrder
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeLogUniformCutoff
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Case I, (14.23): endpoint source bounds

The published predicate `CaseI1423EndpointSourceBounds` omits the source
hypotheses (and even quantifies over `C = 0`), so it is not a valid unconditional
statement.  This file proves the source-faithful version used in Case I.  The source bounds are imported from their proved production producers.  In
particular, neither endpoint inequality is assumed in this module.
-/

private theorem endpoint_sigma11_bound
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ L R : ℝ)
    (N D : ℕ) (s : ℝ)
    (hC : 0 < C) (hD : 0 < (D : ℝ))
    (hlog : 0 < Real.log (D : ℝ))
    (hll : 0 < Real.log (Real.log (D : ℝ)))
    (hσ0 : 0 < sourceSigma (D : ℝ) d)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hE0 : 0 ≤ errorEnvelope H N (D : ℝ) d s)
    (htransport : finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
      L * R * (sourceSigma (D : ℝ) d *
        Real.log (Real.exp 1 * sourceSigma (D : ℝ) d)) *
          errorEnvelope H N (D : ℝ) d s)
    (hscalarMul : K ^ 2 * sourceSigma (D : ℝ) d ^ 3 *
      Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) *
        Real.log (Real.log (D : ℝ)) ≤ (Real.log (D : ℝ)) ^ (1 - Δ))
    (hpowe : (Real.log (D : ℝ)) ^ (-Δ) * Real.log (D : ℝ) =
      (Real.log (D : ℝ)) ^ (1 - Δ)) :
    caseI1423Sigma11Endpoint S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ K s
        (sourceSigma (D : ℝ) d) ≤
      (6 * L * R / (C * Real.exp √K)) *
        caseI1423RemainderUnit
          (sigma12InheritedBudget S H N D ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s)
          (D : ℝ) (sourceSigma (D : ℝ) d) := by
  exact MathlibNt.SieveTheory.caseI1423_endpoint_sigma11_bound
    S H C K d Δ L R N D s hC hD hlog hll hσ0 hL hR hE0 htransport hscalarMul hpowe

private lemma endpoint_sigma12_final_algebra
    (q V K R σ logσ E0 logLog logD : ℝ)
    (hR : 0 ≤ R) (hσ : 0 < σ) (hE0 : 0 ≤ E0)
    (hV : 0 ≤ V) (hLogLog : 0 ≤ logLog)
    (hfront : V * q ≤ V * 2 * R * σ * logσ * E0)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD) :
    q * σ * V * 6 * K ^ 2 * logLog ≤
      R * E0 * V * logD * 12 / σ := by
  exact MathlibNt.SieveTheory.caseI1423_endpoint_sigma12_final_algebra
    q V K R σ logσ E0 logLog logD hR hσ hE0 hV hLogLog hfront hscalar

/-- Honest endpoint-source statement with a `D` threshold uniform in `N` and
`s`.  Both constants and the eventual threshold precede the pointwise Case-I
source-window hypotheses. -/
def CaseI1423EndpointSourceBoundsSourceLargeLog
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ : ℝ) : Prop :=
  ∃ A11 A12 : ℝ, 0 ≤ A11 ∧ 0 ≤ A12 ∧
    ∀ (D N : ℕ) (s : ℝ), 3 ≤ D →
      K ^ 2 * sourceSigma (D : ℝ) d ^ 3 *
          Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) *
          Real.log (Real.log (D : ℝ)) /
          (Real.log (D : ℝ)) ^ (1 - Δ) ≤ 1 →
      2 ≤ N → 2 ≤ s →
      s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) →
        s ≤ sourceSigma (D : ℝ) d →
        let σ := sourceSigma (D : ℝ) d
        let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
        let B := sigma12InheritedBudget S H N D z C K d Δ s
        caseI1423Sigma11Endpoint S N D z K s σ ≤
            A11 * caseI1423RemainderUnit B (D : ℝ) σ ∧
          caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
            A12 * caseI1423RemainderUnit B (D : ℝ) σ

/-- Closure of the two endpoint source bounds. -/
theorem caseI1423EndpointSourceBounds_of_sourceScalar
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ : ℝ)
    (hH : Section13HatSourceContract H)
    (hC : 0 < C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (_hd : 7 / (1 - Δ) < d) :
    CaseI1423EndpointSourceBoundsSourceLargeLog S H C K d Δ := by
  obtain ⟨L, hL, hfinite⟩ :=
    finiteSourceLayer_pred_le_uniform_oppositeHat
      (lemma132_finiteLayerHatUniform_slack hH)
  obtain ⟨R, hR, hratio⟩ :=
    proposition131iii_uniform_reverse_adjacent_ratio_of_source hH
  let E : ℝ := Real.exp (Real.sqrt K)
  let A11 : ℝ := 6 * L * R / (C * E)
  let A12 : ℝ := 12 * R
  have hE : 0 < E := Real.exp_pos _
  refine ⟨A11, A12, by dsimp [A11]; positivity, by dsimp [A12]; positivity, ?_⟩
  intro D N s hD3 hscalar hN hs hdom
  have hs0 : 0 < s := by linarith
  have hsm0 : 0 < s - 1 := by linarith
  have hdelta : (s / (s - 1)) ^ Δ ≤ 2 := by
    have hb : s / (s - 1) ≤ 2 := by
      apply (div_le_iff₀ hsm0).2
      linarith
    have hb1 : 1 ≤ s / (s - 1) := by
      apply (le_div_iff₀ hsm0).2
      linarith
    calc
      (s / (s - 1)) ^ Δ ≤ (2 : ℝ) ^ Δ :=
        Real.rpow_le_rpow (zero_le_one.trans hb1) hb hΔ0.le
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hΔ1.le
      _ = 2 := by norm_num
  intro hsσ
  dsimp only
  let σ := sourceSigma (D : ℝ) d
  let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let T := H.T (ErrorSign.ofDepth N) s
  let E0 := errorEnvelope H N (D : ℝ) d s
  have hD : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD
  have hlog_gt_one : 1 < Real.log (D : ℝ) := by
    have : Real.exp 1 < (D : ℝ) := by
      calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
           _ ≤ (D : ℝ) := by exact_mod_cast (show 3 ≤ D by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity : 0 < (D : ℝ))).2 this
  have hll : 0 < Real.log (Real.log (D : ℝ)) := Real.log_pos hlog_gt_one
  have hσ2 : 2 ≤ σ := hs.trans hsσ
  have hσ0 : 0 < σ := by linarith
  have hlogσ : 0 < Real.log (Real.exp 1 * σ) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hσ0), Real.log_exp]
    have := Real.log_nonneg (by linarith : 1 ≤ σ)
    linarith
  have hE0 : 0 ≤ E0 := by
    dsimp [E0]
    exact errorEnvelope_nonneg H N hD hs0.le
      (hH.positive (ErrorSign.ofDepth N) s hs0).le
  have hrev := hratio (ErrorSign.ofDepth N) s σ hs hsσ
  have hfin := hfinite N s hN hs hdom
  have htransport : finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
      L * R * (σ * Real.log (Real.exp 1 * σ)) * E0 := by
    have hTpos := hH.positive (ErrorSign.ofDepth N) s hs0
    have hquot := (div_le_iff₀ hTpos).mp hrev
    have hpert : s * T ≤ E0 := by
      dsimp [T, E0, errorEnvelope, Section13HatLayers.kappaHat]
      norm_num [Real.rpow_one]
      have hbase : 1 ≤ 1 + s ^ d / Real.log (D : ℝ) := by
        have : 0 ≤ s ^ d / Real.log (D : ℝ) := div_nonneg (Real.rpow_nonneg hs0.le _) hlog.le
        linarith
      have hp := Real.one_le_rpow hbase hs0.le
      have hsp := mul_le_mul_of_nonneg_right hp (mul_nonneg hs0.le hTpos.le)
      simpa [E0, errorEnvelope, Section13HatLayers.kappaHat,
        Real.rpow_one, mul_assoc] using hsp
    calc
      finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
          L * ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1)) := hfin
      _ ≤ L * (s * H.T (ErrorSign.ofDepth N).opposite (s - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith [hL])
        exact mul_le_mul_of_nonneg_right (by linarith)
          (hH.positive _ _ hsm0).le
      _ ≤ L * ((R * (σ * Real.log (Real.exp 1 * σ))) * (s * T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [T, proposition131iiiReverseRatio] at hquot ⊢
        nlinarith [hquot, hTpos.le]
      _ ≤ L * ((R * (σ * Real.log (Real.exp 1 * σ))) * E0) := by gcongr
      _ = L * R * (σ * Real.log (Real.exp 1 * σ)) * E0 := by ring
  have hq : qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ s ≤
      2 * R * (σ * Real.log (Real.exp 1 * σ)) * E0 := by
    have hfixed := caseISigma12_qD_le_fixedFactor_mul_errorEnvelope
      hH.toSection13HatContract N (D := (D : ℝ)) (d := d) (Δ := Δ) (s := s) hD hs
    apply hfixed.trans
    dsimp [caseISigma12QDFixedFactor]
    dsimp [caseISigma12QDFixedFactor, proposition131iiiReverseRatio] at hrev
    have hratio0 : 0 ≤ H.T (ErrorSign.ofDepth N).opposite (s - 1) /
        H.T (ErrorSign.ofDepth N) s := by
      exact div_nonneg (hH.positive _ _ hsm0).le (hH.positive _ _ hs0).le
    have hfac : (s / (s - 1)) ^ Δ *
        (H.T (ErrorSign.ofDepth N).opposite (s - 1) /
          H.T (ErrorSign.ofDepth N) s) ≤
        2 * (R * (σ * Real.log (Real.exp 1 * σ))) := by
      exact mul_le_mul hdelta hrev hratio0 (by positivity)
    exact mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using hfac) hE0
  have hlog1 : 1 ≤ Real.log (D : ℝ) := hlog_gt_one.le
  have hpowden : (Real.log (D : ℝ)) ^ (1 - Δ) ≤ Real.log (D : ℝ) := by
    calc
      (Real.log (D : ℝ)) ^ (1 - Δ) ≤ (Real.log (D : ℝ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
      _ = Real.log (D : ℝ) := by norm_num
  have hpowe : (Real.log (D : ℝ)) ^ (-Δ) * Real.log (D : ℝ) =
      (Real.log (D : ℝ)) ^ (1 - Δ) := by
    calc
      (Real.log (D : ℝ)) ^ (-Δ) * Real.log (D : ℝ) =
          (Real.log (D : ℝ)) ^ (-Δ) * (Real.log (D : ℝ)) ^ (1 : ℝ) := by norm_num
      _ = (Real.log (D : ℝ)) ^ (-Δ + 1) := (Real.rpow_add hlog _ _).symm
      _ = (Real.log (D : ℝ)) ^ (1 - Δ) := by ring_nf
  have hscalarMul : K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
      Real.log (Real.log (D : ℝ)) ≤ (Real.log (D : ℝ)) ^ (1 - Δ) := by
    exact (div_le_one (by positivity)).mp (by simpa [σ] using hscalar)
  constructor
  · dsimp [A11, E, z, σ]
    exact endpoint_sigma11_bound S H C K d Δ L R N D s hC
      (by linarith : 0 < (D : ℝ)) hlog hll hσ0
      (by linarith [hL]) (by linarith [hR]) (by simpa [E0] using hE0)
      (by simpa [σ, E0] using htransport)
      (by simpa [σ] using hscalarMul) hpowe
  · unfold caseI1423Sigma12Endpoint caseI1423RemainderUnit sigma12InheritedBudget
    rw [log_rpow_one_div_sourceSigma (D := (D : ℝ)) (d := d) (by positivity)]
    dsimp [σ, z, A12, E, E0] at hq ⊢
    have hfront := mul_le_mul_of_nonneg_left hq
      (mul_nonneg (mul_nonneg (mul_nonneg hC.le hE.le)
        (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg hlog.le (-Δ)))
    have hscalar12Mul : K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
        Real.log (Real.log (D : ℝ)) ≤ Real.log (D : ℝ) :=
      hscalarMul.trans hpowden
    field_simp [ne_of_gt hlog, ne_of_gt hll, ne_of_gt hσ0] at hfront ⊢
    exact endpoint_sigma12_final_algebra
      (qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ s)
      (suzukiVProduct S (z : ℝ)) K R σ
      (Real.log (Real.exp 1 * σ)) E0 (Real.log (Real.log (D : ℝ)))
      (Real.log (D : ℝ)) (by linarith [hR] : 0 ≤ R) hσ0 hE0
      (suzukiVProduct_pos S (z : ℝ)).le hll.le
      (by simpa [mul_comm] using hfront) hscalar12Mul

/-- Source-large-log endpoint API.  The cutoff is selected before `C`, `K`,
`N`, `D`, and `s`; the only large-parameter hypothesis is the literal Case-I
source inequality. -/
theorem exists_caseI1423EndpointSourceBounds_sourceLargeLog_uniform
    (S : BoundingSieve) (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hΔ0 : 0 < Δ) (hΘ : 0 < Θ)
    (hmargin : Δ + 2 / Θ < 1)
    (hd : 7 / (1 - (Δ + 2 / Θ)) < d) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 C K : ℝ), C1min ≤ C1 → 0 < C → 2 ≤ K →
        ∃ A11 A12 : ℝ, 0 ≤ A11 ∧ 0 ≤ A12 ∧
          ∀ (N D : ℕ) (s : ℝ), 3 ≤ D →
            C1 * K ^ Θ < Real.log (D : ℝ) →
            2 ≤ N → 2 ≤ s →
            s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) →
            s ≤ sourceSigma (D : ℝ) d →
            let σ := sourceSigma (D : ℝ) d
            let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
            let B := sigma12InheritedBudget S H N D z C K d Δ s
            caseI1423Sigma11Endpoint S N D z K s σ ≤
                A11 * caseI1423RemainderUnit B (D : ℝ) σ ∧
              caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
                A12 * caseI1423RemainderUnit B (D : ℝ) σ := by
  obtain ⟨C1min, hC1min, hscalar⟩ :=
    exists_caseI1423_sourceScalar_sourceLargeLog_uniform hΔ0 hΘ hmargin hd
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 C K hC1 hC hK
  have hη0 : 0 < 2 / Θ := by positivity
  have hΔ1 : Δ < 1 := by linarith [hmargin]
  have hdWeak : 7 / (1 - Δ) < d := by
    have hden : 0 < 1 - (Δ + 2 / Θ) := sub_pos.mpr hmargin
    have hdenWeak : 0 < 1 - Δ := by linarith
    have hfrac : 7 / (1 - Δ) ≤ 7 / (1 - (Δ + 2 / Θ)) := by
      apply (div_le_div_iff₀ hdenWeak hden).2
      nlinarith
    exact hfrac.trans_lt hd
  obtain ⟨A11, A12, hA11, hA12, hendpoint⟩ :=
    caseI1423EndpointSourceBounds_of_sourceScalar S H C K d Δ hH hC hΔ0 hΔ1 hdWeak
  refine ⟨A11, A12, hA11, hA12, ?_⟩
  intro N D s hD3 hlarge hN hs hdom hsσ
  exact hendpoint D N s hD3
    (hscalar C1 K (D : ℝ) hC1 hK (by exact_mod_cast (show 2 ≤ D by omega)) hlarge)
    hN hs hdom hsσ


end MathlibNt.SieveTheory
