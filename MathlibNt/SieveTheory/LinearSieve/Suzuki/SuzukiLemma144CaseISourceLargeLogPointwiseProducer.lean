import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEndpointSourceLargeLogUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0CaseBUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeCoefficientUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SourceLargeLogFixedThreshold
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIFinalProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIMovingSuccessor

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 3000000

private lemma endpoint_sigma11_front_rearrange
    (V K F logD σ : ℝ) (hlogD : 0 < logD) (hσ : 0 < σ) :
    V * (6 * K ^ 2 * F / (logD / σ)) =
      6 * V * (K ^ 2 * σ / logD) * F := by
  field_simp [ne_of_gt hlogD, ne_of_gt hσ]

private lemma endpoint_sigma11_collect
    (V K L R σ logσ E0 logD : ℝ) :
    6 * V * (K ^ 2 * σ / logD) *
        (L * R * (σ * logσ) * E0) =
      6 * L * R * V * E0 * (K ^ 2 * σ ^ 2 * logσ / logD) := by
  ring

private lemma endpoint_sigma11_budget_identity
    (L R C E V E0 logPow logLog σ : ℝ)
    (hC : 0 < C) (hE : 0 < E) (hLogLog : 0 < logLog)
    (hσ : 0 < σ) :
    6 * L * R * V * E0 * (logPow / (logLog * σ)) =
      (6 * L * R / (C * E)) *
        (C * E * V * logPow * E0 / (logLog * σ)) := by
  field_simp [ne_of_gt hC, ne_of_gt hE, ne_of_gt hLogLog, ne_of_gt hσ]

private lemma endpoint_sigma11_normalization
    (K σ logσ logD logLog Δ : ℝ)
    (hlog : 0 < logD) (hll : 0 < logLog) (hσ : 0 < σ)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD ^ (1 - Δ))
    (hpowe : logD ^ (-Δ) * logD = logD ^ (1 - Δ)) :
    K ^ 2 * σ ^ 2 * logσ / logD ≤
      logD ^ (-Δ) / (logLog * σ) := by
  apply (div_le_div_iff₀ hlog (mul_pos hll hσ)).2
  calc
    K ^ 2 * σ ^ 2 * logσ * (logLog * σ) =
      K ^ 2 * σ ^ 3 * logσ * logLog := by ring
    _ ≤ logD ^ (1 - Δ) := hscalar
    _ = logD ^ (-Δ) * logD := hpowe.symm

private lemma endpoint_sigma11_core
    (V K F logD σ L R logσ E0 logPow logLog C E : ℝ)
    (hlog : 0 < logD) (hσ : 0 < σ) (hC : 0 < C)
    (hE : 0 < E) (hll : 0 < logLog)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hR : 0 ≤ R) (hE0 : 0 ≤ E0)
    (htransport : F ≤ L * R * (σ * logσ) * E0)
    (hnorm : K ^ 2 * σ ^ 2 * logσ / logD ≤
      logPow / (logLog * σ)) :
    V * (6 * K ^ 2 * F / (logD / σ)) ≤
      (6 * L * R / (C * E)) *
        (C * E * V * logPow * E0 / (logLog * σ)) := by
  calc
    V * (6 * K ^ 2 * F / (logD / σ)) =
      6 * V * (K ^ 2 * σ / logD) * F :=
        endpoint_sigma11_front_rearrange _ _ _ _ _ hlog hσ
    _ ≤ 6 * V * (K ^ 2 * σ / logD) *
        (L * R * (σ * logσ) * E0) := by gcongr
    _ = 6 * L * R * V * E0 *
        (K ^ 2 * σ ^ 2 * logσ / logD) :=
          endpoint_sigma11_collect _ _ _ _ _ _ _ _
    _ ≤ 6 * L * R * V * E0 * (logPow / (logLog * σ)) := by gcongr
    _ = (6 * L * R / (C * E)) *
        (C * E * V * logPow * E0 / (logLog * σ)) :=
          endpoint_sigma11_budget_identity _ _ _ _ _ _ _ _ _ hC hE hll hσ

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
  unfold caseI1423Sigma11Endpoint caseI1423RemainderUnit sigma12InheritedBudget
  rw [log_rpow_one_div_sourceSigma (D := (D : ℝ)) (d := d) hD]
  have hnorm : K ^ 2 * sourceSigma (D : ℝ) d ^ 2 *
      Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) / Real.log (D : ℝ) ≤
      (Real.log (D : ℝ)) ^ (-Δ) /
        (Real.log (Real.log (D : ℝ)) * sourceSigma (D : ℝ) d) := by
    exact endpoint_sigma11_normalization _ _ _ _ _ _ hlog hll hσ0
      hscalarMul hpowe
  exact endpoint_sigma11_core _ _ _ _ _ _ _ _ _ _ _ _ _
    hlog hσ0 hC (Real.exp_pos _) hll
    (suzukiVProduct_pos S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)).le
    hL hR hE0 htransport hnorm


private lemma endpoint_sigma12_final_algebra_pointwise
    (q V K R σ logσ E0 logLog logD : ℝ)
    (hR : 0 ≤ R) (hσ : 0 < σ) (hE0 : 0 ≤ E0)
    (hV : 0 ≤ V) (hLogLog : 0 ≤ logLog)
    (hfront : V * q ≤ V * 2 * R * σ * logσ * E0)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD) :
    q * σ * V * 6 * K ^ 2 * logLog ≤
      R * E0 * V * logD * 12 / σ := by
  have hfactor : 0 ≤ 6 * K ^ 2 * logLog * σ := by positivity
  have hbudgetFactor : 0 ≤ 12 * R * E0 * V / σ := by positivity
  calc
    q * σ * V * 6 * K ^ 2 * logLog =
        (6 * K ^ 2 * logLog * σ) * (V * q) := by ring
    _ ≤ (6 * K ^ 2 * logLog * σ) *
        (V * 2 * R * σ * logσ * E0) :=
          mul_le_mul_of_nonneg_left hfront hfactor
    _ = (12 * R * E0 * V / σ) *
        (K ^ 2 * σ ^ 3 * logσ * logLog) := by
          field_simp [ne_of_gt hσ]
          ring
    _ ≤ (12 * R * E0 * V / σ) * logD :=
      mul_le_mul_of_nonneg_left hscalar hbudgetFactor
    _ = R * E0 * V * logD * 12 / σ := by ring

/-- Sharp pointwise endpoint bounds with the two explicit coefficients exposed. -/
theorem caseI1423EndpointSourceBounds_sharp_of_source
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ L R : ℝ)
    (hH : Section13HatSourceContract H) (hC : 0 < C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (_hd : 7 / (1 - Δ) < d)
    (hL : 1 ≤ L)
    (hfinite : ∀ (N : ℕ) (s : ℝ), 2 ≤ N → 2 ≤ s →
      s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) →
      finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
        L * ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1)))
    (hR : 1 ≤ R)
    (hratio : ∀ (sign : ErrorSign) (s σ : ℝ), 2 ≤ s → s ≤ σ →
      proposition131iiiReverseRatio H sign s ≤
        R * (σ * Real.log (Real.exp 1 * σ))) :
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
          (6 * L * R / (C * Real.exp (Real.sqrt K))) *
            caseI1423RemainderUnit B (D : ℝ) σ ∧
        caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
          (12 * R) * caseI1423RemainderUnit B (D : ℝ) σ := by
  let E : ℝ := Real.exp (Real.sqrt K)
  let A11 : ℝ := 6 * L * R / (C * E)
  let A12 : ℝ := 12 * R
  have hE : 0 < E := Real.exp_pos _
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
  have hll : 0 < Real.log (Real.log (D : ℝ)) := by
    apply Real.log_pos
    have : Real.exp 1 < (D : ℝ) := by
      calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
           _ ≤ (D : ℝ) := by exact_mod_cast (show 3 ≤ D by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity : 0 < (D : ℝ))).2 this
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
  have hlog1 : 1 ≤ Real.log (D : ℝ) := by
    have he : Real.exp 1 < (D : ℝ) := by
      calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
           _ ≤ (D : ℝ) := by exact_mod_cast (show 3 ≤ D by omega)
    exact ((Real.lt_log_iff_exp_lt (by positivity : 0 < (D : ℝ))).2 he).le
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
  · exact endpoint_sigma11_bound S H C K d Δ L R N D s hC
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
    have hscalar12 : K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
        Real.log (Real.log (D : ℝ)) / Real.log (D : ℝ) ≤ 1 := by
      calc
        K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
            Real.log (Real.log (D : ℝ)) / Real.log (D : ℝ) ≤
          K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
            Real.log (Real.log (D : ℝ)) /
              (Real.log (D : ℝ)) ^ (1 - Δ) := by
                apply div_le_div_of_nonneg_left (by positivity) (by positivity) hpowden
        _ ≤ 1 := hscalar
    have hscalar12Mul : K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
        Real.log (Real.log (D : ℝ)) ≤ Real.log (D : ℝ) :=
      (div_le_one hlog).mp hscalar12
    field_simp [ne_of_gt hlog, ne_of_gt hll, ne_of_gt hσ0] at hfront ⊢
    exact endpoint_sigma12_final_algebra_pointwise
      (qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ s)
      (suzukiVProduct S (z : ℝ)) K R σ
      (Real.log (Real.exp 1 * σ)) E0 (Real.log (Real.log (D : ℝ)))
      (Real.log (D : ℝ)) (by linarith [hR] : 0 ≤ R) hσ0 hE0
      (suzukiVProduct_pos S (z : ℝ)).le hll.le
      (by simpa [mul_comm] using hfront) hscalar12Mul


private theorem caseI_inheritedCoordinate_gt_pointwise
    {D p : ℕ} {s : ℝ}
    (hp : 2 ≤ p) (hD : 1 < D) (hs : 0 < s)
    (hupper : (p : ℝ) < (D : ℝ) ^ (1 / s)) :
    s - 1 < inheritedCoordinate D p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hDR : (0 : ℝ) < (D : ℝ) := by positivity
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hloglt := Real.strictMonoOn_log (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
    (show (D : ℝ) ^ (1 / s) ∈ Set.Ioi 0 by exact Real.rpow_pos_of_pos hDR _)
    hupper
  rw [Real.log_rpow hDR] at hloglt
  unfold inheritedCoordinate
  have hsne : s ≠ 0 := ne_of_gt hs
  have : s < Real.log (D : ℝ) / Real.log (p : ℝ) := by
    rw [lt_div_iff₀ hlogp]
    field_simp [hsne] at hloglt ⊢
    nlinarith
  linarith

/-- Production strict Case-I pointwise producer, uniform in the bounding sieve.
The cutoff constants precede `S,C1,C,K,M,D,s`; the predecessor induction
threshold is literally `2`. -/
theorem exists_lemma14_4_caseI_final_producer_sourceLargeLog_pointwise_uniform_in_S
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min CB : ℝ, 1 ≤ C1min ∧ 0 < CB ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (M D : ℕ) (s : ℝ),
        C1min ≤ C1 → max 3 CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        2 ≤ M →
        s ∈ KappaOneModel.parityDomain 2 M →
        s - 1 ∈ KappaOneModel.parityDomain 2 (M - 1) →
        2 ≤ s → 2 + (ErrorSign.ofDepth M).epsilon ≤ s →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        s ≤ sourceSigma (D : ℝ) d →
        H.betaHat + (ErrorSign.ofDepth M).epsilon < s →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / s)⌉₊ *
            finiteSourceLayer 1 2 M s +
          sigma12InheritedBudget S H M D
            ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s := by
  have hd1 : 1 < d := by
    have hden : 0 < 1 - Δ := sub_pos.mpr hsrc.hDelta_lt
    have hdenlt : 1 - Δ < 1 := by linarith [hsrc.hDelta_pos]
    have hseven : 7 < 7 / (1 - Δ) := by
      apply (lt_div_iff₀ hden).2
      nlinarith
    linarith [hsrc.h14_1]
  obtain ⟨L, hL, hfinite⟩ :=
    finiteSourceLayer_pred_le_uniform_oppositeHat
      (lemma132_finiteLayerHatUniform_slack hH)
  obtain ⟨R, hR, hratio⟩ :=
    proposition131iii_uniform_reverse_adjacent_ratio_of_source hH
  let Amax : ℝ := 1 + 2 * L * R + 12 * R
  have hAmax : 0 ≤ Amax := by dsimp [Amax]; positivity
  obtain ⟨C1coef, hC1coef, hcoef⟩ :=
    exists_caseISourceOrderCoefficient_sourceLargeLog_uniform
      hAmax hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1 hsrc.hTheta_pos
  obtain ⟨C1scalar, hC1scalar, hscalar⟩ :=
    exists_caseI1423_sourceScalar_sourceLargeLog_uniform_of_source hsrc
  obtain ⟨C1B, CB, hC1B, hCB, hcaseB⟩ :=
    claim145_caseB_sigmaZero_uniform_strict_in_S H hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hsrc.one_le_theta hH
  obtain ⟨D12, hD12pos, h12⟩ :=
    exists_sigmaTwelve_internal_contraction_binderUniform_in_S
      (H := H) hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨D146, hD146pos, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma
      hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨Dg, hDgpos, hg⟩ := exists_caseI_preThreshold_geometry_packet d hd1
  obtain ⟨Drec, hrec⟩ := eventually_atTop.1
    (eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform hd1)
  obtain ⟨Derr, herr⟩ := eventually_atTop.1
    (eventually_caseI_errorEnvelope_transport_uniform_in_S
      H hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt)
  obtain ⟨Dpkt, hpkt⟩ := eventually_atTop.1
    (eventually_caseI_strict_pointwise_packet_uniform_in_S H hH hd1 hsrc.hDelta_pos
      (show 2 ≤ (2 : ℕ) by norm_num))
  let Dcut : ℝ := max 4 (max D12 (max D146 (max Dg
    (max (Drec : ℝ) (max (Derr : ℝ) (Dpkt : ℝ))))))
  have hDcut : 0 < Dcut := (by norm_num : (0 : ℝ) < 4).trans_le (le_max_left _ _)
  obtain ⟨C1cut, hC1cut, hcut⟩ :=
    exists_sourceLargeLog_fixedThreshold_of_source hsrc Dcut hDcut
  let C1min : ℝ := max 1 (max C1coef (max C1scalar (max C1B C1cut)))
  have hC1min : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, CB, hC1min, hCB, ?_⟩
  intro S C1 C K M D s hC1 hCcommon hK hlocal hM hsdom hspred hs hsLower
    hlarge hsσ hthreshold hglobal
  have hCBC : CB ≤ C := (le_max_right 3 CB).trans hCcommon
  have hC3 : (3 : ℝ) ≤ C := (le_max_left 3 CB).trans hCcommon
  have hCpos : 0 < C := by linarith
  have hcoefC1 : C1coef ≤ C1 :=
    (le_max_left C1coef (max C1scalar (max C1B C1cut))).trans
      ((le_max_right 1 _).trans hC1)
  have hscalarC1 : C1scalar ≤ C1 :=
    (le_max_left C1scalar (max C1B C1cut)).trans
      ((le_max_right C1coef _).trans ((le_max_right 1 _).trans hC1))
  have hcaseBC1 : C1B ≤ C1 :=
    (le_max_left C1B C1cut).trans
      ((le_max_right C1scalar _).trans
        ((le_max_right C1coef _).trans ((le_max_right 1 _).trans hC1)))
  have hcutC1 : C1cut ≤ C1 :=
    (le_max_right C1B C1cut).trans
      ((le_max_right C1scalar _).trans
        ((le_max_right C1coef _).trans ((le_max_right 1 _).trans hC1)))
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by
      by_contra hn
      have hD0 : D = 0 := by omega
      subst D
      norm_num at hlarge
      have hC10 : 0 ≤ C1 :=
        (show (0 : ℝ) ≤ 1 by norm_num).trans (hC1min.trans hC1)
      have hKpow : 0 ≤ K ^ Θ := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg hC10 hKpow])
  have hDcutD : Dcut < (D : ℝ) := hcut C1 K (D : ℝ) hcutC1 hK hDpos hlarge
  have hD4 : 4 ≤ D := by
    exact_mod_cast ((le_max_left 4 _).trans hDcutD.le)
  have hD3 : 3 ≤ D := by omega
  have hD2 : 2 ≤ D := by omega
  have hD12 : D12 ≤ (D : ℝ) :=
    (le_max_left D12 _).trans ((le_max_right 4 _).trans hDcutD.le)
  have hD146 : D146 ≤ (D : ℝ) :=
    (le_max_left D146 _).trans
      ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le))
  have hDg : Dg ≤ (D : ℝ) :=
    (le_max_left Dg _).trans
      ((le_max_right D146 _).trans
        ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le)))
  have hDrec : Drec ≤ D := by
    exact_mod_cast ((le_max_left (Drec : ℝ) _).trans
      ((le_max_right Dg _).trans
        ((le_max_right D146 _).trans
          ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le)))))
  have hDerr : Derr ≤ D := by
    exact_mod_cast ((le_max_left (Derr : ℝ) (Dpkt : ℝ)).trans
      ((le_max_right (Drec : ℝ) _).trans
        ((le_max_right Dg _).trans
          ((le_max_right D146 _).trans
            ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le))))))
  have hDpkt : Dpkt ≤ D := by
    exact_mod_cast ((le_max_right (Derr : ℝ) (Dpkt : ℝ)).trans
      ((le_max_right (Drec : ℝ) _).trans
        ((le_max_right Dg _).trans
          ((le_max_right D146 _).trans
            ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le))))))
  have g := hg D M hDg s hs hsσ
  have hrecursiveD := hrec D hDrec S
  have hinheritedForError : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
      (sourceSigma (D : ℝ) d) s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp
    have hp' := hp
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    apply parityDomain_mono hspred
    exact (caseI_inheritedCoordinate_gt_pointwise
      (Nat.prime_of_mem_primeFactors hp'.1).two_le (by omega)
      (by linarith) hp'.2.2).le
  have herrorD := herr D hDerr S
  have herror := herrorD M s hs hinheritedForError (hrecursiveD s hs)
  obtain ⟨hprime, hscale, hinherited, hsource, herror', hceil, hT, h1413⟩ :=
    hpkt D hDpkt S M s hM hspred hs herror
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊ := rfl
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hprimeZ : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp; exact hprime p (Finset.mem_filter.mp hp).1
  have toFull : ∀ p, p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s →
      p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ s := by
    intro p hp
    simpa only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] using
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_filter.mp hp).2⟩
  have hscaleZ : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S z) D 2 σ s := by
    intro p hp; exact hscale p (toFull p hp)
  have hinheritedZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp; exact hinherited p (toFull p hp)
  have hsourceZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      finiteSourceLayer 1 2 (M - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (M - 1) (inheritedCoordinate D p) := by
    intro p hp; exact hsource p (toFull p hp)
  have herrorZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p) := by
    intro p hp; exact herror' p (toFull p hp)
  have hrecursiveZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
    intro p hp; exact hrecursiveD s hs p (toFull p hp)
  have hpoint : PointwiseInductionContract
      (suzukiSupportedBelow S z) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ M D σ s :=
    pointwiseInductionContract_of_movingDomainIH S H C K d Δ M D 2 σ s
      (by norm_num) hprimeZ hscaleZ hinheritedZ
      (by intro p _; exact (suzukiVProduct_pos S p).le) hCpos.le hsourceZ herrorZ
      hrecursiveZ hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (suzukiActualT S) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ M D σ s
    (ne_of_gt (suzukiVProduct_pos S z))
    (by intro p hp; have hpS := (Finset.mem_filter.mp hp).1
        exact (S.nu_pos_of_prime p (hprimeZ p hpS)
          ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le) hpoint
  have h149 : suzukiActualT S M D z =
      suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / s)) +
          suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / s)) := by
    by_cases hOddM : Odd M
    · have hs3 : 3 ≤ s := by
        norm_num [ErrorSign.ofDepth, hOddM, ErrorSign.epsilon] at hsLower
        exact hsLower
      exact suzuki_equation14_9_natCeil S hM (by omega) hs3 hz g.hpowerOrder
    · exact suzuki_equation14_9_strict S hM
        (by intro hodd; exact (hOddM hodd).elim) g.hpowerOrder
  have h11raw := caseI_sigmaEleven_le_finiteSourceLayer_add_endpoint
    (S := S) (β := (2 : ℝ)) (s := s) (τ := s) (σ := σ)
    (K := K) (N := M) (D := D) (z := z)
    (by norm_num) hsdom hspred le_rfl hsσ hDreal g.hpowerS g.hpowerS
      g.hpowerSigma g.hpowerOrder le_rfl hz hK hlocal
  have h11 : sigmaEleven (suzukiSupportedBelow S z) S.nu
      (fun p => suzukiVProduct S p) (suzukiVProduct S z) 2 M D σ s ≤
      suzukiVProduct S z * finiteSourceLayer 1 2 M s +
        caseI1423Sigma11Endpoint S M D z K s σ := by
    simpa [caseI1423Sigma11Endpoint, div_self (ne_of_gt (by linarith : 0 < s))] using h11raw
  obtain ⟨q12, hq12, _h12raw, h12q⟩ :=
    h12 S C K hK hlocal hCpos.le D M s z hD12 (by linarith) hsLower
      g.hsigma hsσ hDreal g.hpowerS g.hpowerSigma g.hpowerOrder hz
      hthreshold.le hceil hT h1413
  have hcarrier : sigmaOneCarrier (suzukiSupportedBelow S z) D σ s =
      sigmaOneCarrier S.prodPrimes.primeFactors D σ s := by
    ext p
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpS, _⟩, hpw, hpv⟩; exact ⟨hpS, hpw, hpv⟩
    · rintro ⟨hpS, hpw, hpv⟩
      exact ⟨⟨hpS, (nat_lt_natCeil_iff_lt_real
        (natCast_rpow_one_div_pos (by omega) s) hz).2 hpv⟩, hpw, hpv⟩
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ s ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ s +
          caseI1423Sigma12Endpoint S H M D z C K d Δ s σ := by
    rw [show suzukiSupportedBelow S z =
      S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl]
    rw [sigmaTwelve_supportedBelow_eq_full S
      (fun p => suzukiVProduct S (p : ℝ))
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S (z : ℝ)) C K Δ M D z σ s (Nat.le_ceil _)]
    simpa [σ, caseI1423Sigma12Endpoint, sigma12EndpointRemainder,
      div_self (ne_of_gt (by linarith : 0 < s))] using h12q
  have hscalarD := hscalar C1 K (D : ℝ) hscalarC1 hK
    (by exact_mod_cast hD2) hlarge
  have hend := caseI1423EndpointSourceBounds_sharp_of_source
    S H C K d Δ L R hH hCpos hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1
      hL hfinite hR hratio D M s hD3 hscalarD hM hs hspred hsσ
  have hzσ : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) :=
    g.hpowerOrder.trans (Nat.le_ceil _)
  have hzeroRaw := hcaseB S C1 C K M D z hcaseBC1 hCBC hK hlocal hD2
    hlarge hM hzσ
  have hzeroDirect : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      caseISigmaZeroDirectRemainder S H M D CB K d Δ := by
    have hzraw := hzeroRaw
    have heq : (CB / C) * (C * claim14_5Scale S H M (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) =
        caseISigmaZeroDirectRemainder S H M D CB K d Δ := by
      unfold caseISigmaZeroDirectRemainder
      field_simp [ne_of_gt hCpos]
    rw [heq] at hzraw
    simpa [σ] using hzraw
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hDreal
  have hll : 0 < Real.log (Real.log (D : ℝ)) := by
    apply Real.log_pos
    have he : Real.exp 1 < (D : ℝ) := by
      calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
           _ ≤ (D : ℝ) := by exact_mod_cast hD3
    exact (Real.lt_log_iff_exp_lt hDpos).2 he
  have hlllog : Real.log (Real.log (D : ℝ)) ≤ Real.log (D : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hlog]
  have hzD : (z : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (Nat.ceil_le.mpr (by
      calc
        (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hDreal.le
          have hs0 : 0 < s := by linarith
          exact (div_le_one (by linarith : 0 < s)).2 (by linarith)
        _ = (D : ℝ) := by norm_num))
  have hEσ : 0 ≤ errorEnvelope H M (D : ℝ) d σ :=
    errorEnvelope_nonneg H M hDreal (by dsimp [σ]; linarith [g.hsigma])
      (hH.positive _ _ (by dsimp [σ]; linarith [g.hsigma])).le
  have hzeroSource := caseISigmaZeroDirectRemainder_le_sourceOrder
    (S := S) (H := H) (N := M) (D := D) (z := z)
    (C := C) (C145 := CB) (K := K) (d := d) (Δ := Δ)
    hDreal hll hlllog hzD (by simpa [σ] using (show (0 : ℝ) <
      sourceSigma (D : ℝ) d by linarith [g.hsigma]))
    hCpos hCB.le (by simpa [σ] using hEσ)
  have hi := (h146 (D : ℝ) hD146).1
  have hEtransport : errorEnvelope H M (D : ℝ) d σ ≤
      errorEnvelope H M (D : ℝ) d s := by
    apply errorEnvelope_endpoint_le_of_claim14_6 hH.toSection13HatContract hDreal hi
    rw [hH.betaHat_eq]
    exact ⟨hsLower, by simpa [σ] using hsσ⟩
  have hbudgetTransport : sigma12InheritedBudget S H M D z C K d Δ σ ≤
      sigma12InheritedBudget S H M D z C K d Δ s := by
    unfold sigma12InheritedBudget
    apply mul_le_mul_of_nonneg_left hEtransport
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hCpos.le (Real.exp_pos _).le)
        (suzukiVProduct_pos S (z : ℝ)).le)
      (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _)
  have hzeroUnit : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      (CB / C) * caseI1423RemainderUnit
        (sigma12InheritedBudget S H M D z C K d Δ s) (D : ℝ) σ := by
    apply hzeroDirect.trans
    calc
      caseISigmaZeroDirectRemainder S H M D CB K d Δ ≤
          caseISourceOrderCoefficient (CB / C) (D : ℝ) d *
            sigma12InheritedBudget S H M D z C K d Δ σ := hzeroSource
      _ ≤ caseISourceOrderCoefficient (CB / C) (D : ℝ) d *
            sigma12InheritedBudget S H M D z C K d Δ s := by
        apply mul_le_mul_of_nonneg_left hbudgetTransport
        unfold caseISourceOrderCoefficient
        exact div_nonneg (div_nonneg hCB.le hCpos.le)
          (mul_nonneg hll.le (by linarith [g.hsigma]))
      _ = _ := by
        simp [caseISourceOrderCoefficient, caseI1423RemainderUnit, σ]
        ring
  have hAactual : 0 ≤ CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R := by positivity
  have hAupper : CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R ≤ Amax := by
    have hb := caseI_endpointCoefficient_le_commonScale
      (A := (1 : ℝ)) (C := C) (C145 := CB) (K := K) (L := L) (R := R)
      (by norm_num) hC3 (by simpa using hCBC) (by linarith [hL]) (by linarith [hR])
    norm_num at hb
    simpa [Amax] using hb
  obtain ⟨qgap, hqgap, hcoefGap⟩ := hcoef C1 K (D : ℝ)
    (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R)
    hcoefC1 hK (by exact_mod_cast hD2) hAactual hAupper hlarge
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H M D z C K d Δ s := by
    unfold sigma12InheritedBudget
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCpos.le (Real.exp_pos _).le)
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _))
      (errorEnvelope_nonneg H M hDreal (by linarith)
        (hH.positive _ _ (by linarith)).le)
  have hunit : (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R) *
        caseI1423RemainderUnit
          (sigma12InheritedBudget S H M D z C K d Δ s) (D : ℝ) σ =
      caseISourceOrderCoefficient
          (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R)
          (D : ℝ) d * sigma12InheritedBudget S H M D z C K d Δ s := by
    simp [caseI1423RemainderUnit, caseISourceOrderCoefficient, σ]
    ring
  have hside : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        caseI1423Sigma11Endpoint S M D z K s σ +
        caseI1423Sigma12Endpoint S H M D z C K d Δ s σ ≤
      (1 - q12.ρ) * sigma12InheritedBudget S H M D z C K d Δ s := by
    have hsrcBound := add_le_add (add_le_add hzeroUnit hend.1) hend.2
    calc
      _ ≤ (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R) *
          caseI1423RemainderUnit
            (sigma12InheritedBudget S H M D z C K d Δ s) (D : ℝ) σ := by
        linarith
      _ = _ := hunit
      _ ≤ (1 - qgap.ρ) * sigma12InheritedBudget S H M D z C K d Δ s :=
        mul_le_mul_of_nonneg_right hcoefGap hbudget
      _ = _ := by rw [hqrho]
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := M) S hD4 hs hz
  have h2 : suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / s)) = 0 := by
    simpa [lemma144_realTau_eq_s_of_caseI hD4 hs] using h2raw
  have hmiddle : suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / s)) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S z) 2 M D σ s +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ M D σ s := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S) M D σ s ≤ _
    exact h10
  rw [h149, h2]
  linarith [hzeroDirect, hmiddle, h11, h12qSupported, hside]

/-- Compatibility specialization of the producer uniform in `S`. -/
theorem exists_lemma14_4_caseI_final_producer_sourceLargeLog_pointwise
    (S : BoundingSieve) (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min CB : ℝ, 1 ≤ C1min ∧ 0 < CB ∧
      ∀ (C1 C K : ℝ) (M D : ℕ) (s : ℝ),
        C1min ≤ C1 → max 3 CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        2 ≤ M →
        s ∈ KappaOneModel.parityDomain 2 M →
        s - 1 ∈ KappaOneModel.parityDomain 2 (M - 1) →
        2 ≤ s → 2 + (ErrorSign.ofDepth M).epsilon ≤ s →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        s ≤ sourceSigma (D : ℝ) d →
        H.betaHat + (ErrorSign.ofDepth M).epsilon < s →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / s)⌉₊ *
            finiteSourceLayer 1 2 M s +
          sigma12InheritedBudget S H M D
            ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s := by
  obtain ⟨C1min, CB, hC1min, hCB, hall⟩ :=
    exists_lemma14_4_caseI_final_producer_sourceLargeLog_pointwise_uniform_in_S
      H hH hsrc
  exact ⟨C1min, CB, hC1min, hCB, hall S⟩



end MathlibNt.SieveTheory
