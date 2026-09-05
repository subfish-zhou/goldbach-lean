import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIPositiveEndpointPacket
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaDecay
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIILambdaShortInterval

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000
/-- At the exact source point `y = D^(1/3)`, the integral contribution pays
both the cubic lambda comparison and the product-ratio excess. -/
theorem caseIIPositiveDeltaIntegralPart_source_exact_relative
    (H : Section13HatLayers) {N : ℕ} {D d Δ σ C K s : ℝ}
    (hD : 1 < D) (hs : 0 < s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hiii : (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
      (1 - 1 / σ) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) D d 0 3)
    (hcubic : lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
      perturbation D d 0 3 *
        lambda H (ErrorSign.ofDepth N) D d 0 s) :
    caseIIPositiveDeltaIntegralPart H N D (D ^ (1 / (3 : ℝ)))
        d Δ σ C K s ≤
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
        (Real.log D) ^ (-Δ) *
        ((1 + 3 * K / Real.log D) *
          (1 - 1 / σ) ^ (1 - Δ) * perturbation D d 0 3) := by
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  let R : ℝ := perturbation D d 0 3
  let E : ℝ := errorEnvelope H N D d s
  let L : ℝ := (Real.log D) ^ (-Δ)
  let P : ℝ := C * Real.exp (Real.sqrt K)
  let I : ℝ := ∫ t in (3 : ℝ)..σ,
    qD H (ErrorSign.ofDepth N).opposite D d Δ t
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hlogy : Real.log (D ^ (1 / (3 : ℝ))) = (1 / 3 : ℝ) * Real.log D := by
    rw [Real.log_rpow (zero_lt_one.trans hD)]
  have hratio : 1 + K / Real.log (D ^ (1 / (3 : ℝ))) =
      1 + 3 * K / Real.log D := by
    rw [hlogy]
    field_simp [ne_of_gt hlog]
    <;> ring
  have hlambda : lambda H (ErrorSign.ofDepth N) D d 0 s = s * E := by
    dsimp [E]
    unfold lambda errorEnvelope
    norm_num
    ring
  have hI : (1 / s) * I ≤ (c * R) * E := by
    have hchain : I ≤ c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s) := by
      calc
        I ≤ c * lambda H (ErrorSign.ofDepth N) D d 0 3 := by
          simpa [I, c] using hiii
        _ ≤ c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s) :=
          mul_le_mul_of_nonneg_left (by simpa [R] using hcubic)
            (by simpa [c] using hcut)
    have hscaled := mul_le_mul_of_nonneg_left hchain (one_div_nonneg.mpr hs.le)
    calc
      (1 / s) * I ≤ (1 / s) *
          (c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s)) := hscaled
      _ = (c * R) * E := by
        rw [hlambda]
        field_simp [ne_of_gt hs]
        <;> ring
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hL : 0 ≤ L := by dsimp [L]; exact Real.rpow_nonneg hlog.le _
  have hr : 0 ≤ 1 + 3 * K / Real.log D := by positivity
  have hscale : 0 ≤ (1 + 3 * K / Real.log D) * P * L := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hI hscale
  rw [caseIIPositiveDeltaIntegralPart, hratio]
  change (3 / s) * (1 + 3 * K / Real.log D) *
      (P * L * ((1 / 3) * I)) ≤
    P * E * L * ((1 + 3 * K / Real.log D) * c * R)
  calc
    _ = ((1 + 3 * K / Real.log D) * P * L) * ((1 / s) * I) := by ring
    _ ≤ ((1 + 3 * K / Real.log D) * P * L) * ((c * R) * E) := hscaled
    _ = _ := by ring
private lemma perturbation_three_le_one_add_seven_ratio
    {D d : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d)
    (hsmall : 3 ^ d ≤ Real.log D) :
    perturbation D d 0 3 ≤ 1 + 7 * (3 ^ d / Real.log D) := by
  let x : ℝ := 3 ^ d / Real.log D
  have hx0 : 0 ≤ x := div_nonneg (Real.rpow_nonneg (by norm_num) _) hlog.le
  have hx1 : x ≤ 1 := (div_le_one hlog).2 hsmall
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hx3 : x ^ 3 ≤ x := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ ≤ x * x := mul_le_mul_of_nonneg_right hx2 hx0
      _ ≤ x := by nlinarith
  rw [perturbation]
  norm_num [Real.rpow_natCast]
  dsimp [x] at *
  nlinarith

/-- Eventually the transported relative integral coefficient pays both the
cubic perturbation and the local product-ratio excess. -/
theorem exists_integral_transport_relative_excess_threshold
    (Δ d K : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 ≤ K) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      (1 + 3 * K / Real.log D) *
            (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            perturbation D d 0 3 -
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) ≤
        (1 - Δ) / (32 * sourceSigma D d) := by
  let p : ℝ := 3 ^ d
  let A : ℝ := 3 * K + 7 * p + 21 * K * p
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hq : 0 < 7 / (1 - Δ) := by positivity
  have hd0 : 0 < d := hq.trans hd
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨Ddec, hDdec, hdec⟩ :=
    exists_sourceSigma_positive_delta_decay_threshold
      Δ d (2 * A) hΔ0 hΔ1 hd (by positivity)
  let X : ℝ := max (max 1 p) (Real.exp 1)
  let Dsize : ℝ := Real.exp X
  have hX1 : 1 ≤ X := (le_max_left 1 p).trans (le_max_left _ (Real.exp 1))
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hDsize : 1 < Dsize := by
    dsimp [Dsize]
    exact Real.one_lt_exp_iff.mpr hXpos
  refine ⟨max Ddec Dsize, lt_of_lt_of_le hDdec (le_max_left _ _), ?_⟩
  intro D hD
  have hDdecD : Ddec ≤ D := (le_max_left _ _).trans hD
  have hDsizeD : Dsize ≤ D := (le_max_right _ _).trans hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hDsizeD
  have hlogX : X ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 (by simpa [Dsize] using hDsizeD)
  have hlog1 : 1 ≤ Real.log D := hX1.trans hlogX
  have hlog : 0 < Real.log D := zero_lt_one.trans_le hlog1
  have hpLog : p ≤ Real.log D :=
    ((le_max_right 1 p).trans (le_max_left _ (Real.exp 1))).trans hlogX
  have hexpLog : Real.exp 1 ≤ Real.log D :=
    (le_max_right (max 1 p) (Real.exp 1)).trans hlogX
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hlog27pos : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
  have hinnerpos : 0 < Real.log (27 * D) := by rw [hlog27D]; positivity
  have hinnerexp : Real.exp 1 < Real.log (27 * D) := by
    rw [hlog27D]
    linarith
  have hll1 : 1 < Real.log (Real.log (27 * D)) :=
    (Real.lt_log_iff_exp_lt hinnerpos).2 hinnerexp
  have hfirst1 : 1 ≤ (Real.log D) ^ (1 / d) :=
    Real.one_le_rpow hlog1 (one_div_nonneg.mpr hd0.le)
  have hsig1 : 1 < sourceSigma D d := by
    dsimp [sourceSigma]
    have hfirstpos : 0 < (Real.log D) ^ (1 / d) := by positivity
    calc
      1 ≤ (Real.log D) ^ (1 / d) := hfirst1
      _ < (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D)) :=
        by simpa only [mul_one] using mul_lt_mul_of_pos_left hll1 hfirstpos
  let sig : ℝ := sourceSigma D d
  let c : ℝ := (1 - 1 / sig) ^ (1 - Δ)
  have hsig0 : 0 < sig := zero_lt_one.trans hsig1
  have hb0 : 0 ≤ 1 - 1 / sig := by
    rw [sub_nonneg, div_le_one hsig0]
    exact hsig1.le
  have hb1 : 1 - 1 / sig ≤ 1 := by
    linarith [one_div_pos.mpr hsig0]
  have hc0 : 0 ≤ c := by dsimp [c]; exact Real.rpow_nonneg hb0 _
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact Real.rpow_le_one hb0 hb1 hβ.le
  have hpert : perturbation D d 0 3 ≤ 1 + 7 * (p / Real.log D) := by
    simpa [p] using perturbation_three_le_one_add_seven_ratio hlog hd0.le hpLog
  let r : ℝ := 1 + 3 * K / Real.log D
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hmain : r * c * perturbation D d 0 3 ≤
      r * c * (1 + 7 * (p / Real.log D)) :=
    mul_le_mul_of_nonneg_left hpert (mul_nonneg hr0 hc0)
  have hu0 : 0 ≤ (Real.log D)⁻¹ := inv_nonneg.mpr hlog.le
  have hu1 : (Real.log D)⁻¹ ≤ 1 := (inv_le_one₀ hlog).2 hlog1
  have huu : (Real.log D)⁻¹ * (Real.log D)⁻¹ ≤ (Real.log D)⁻¹ :=
    mul_le_of_le_one_left hu0 hu1
  have hexcess0 : 0 ≤ r * (1 + 7 * (p / Real.log D)) - 1 := by
    have hku : 0 ≤ 3 * K / Real.log D := by positivity
    have hpu : 0 ≤ 7 * p / Real.log D := by positivity
    calc
      0 ≤ 3 * K / Real.log D + 7 * p / Real.log D +
          (3 * K / Real.log D) * (7 * p / Real.log D) := by positivity
      _ = r * (1 + 7 * (p / Real.log D)) - 1 := by
        dsimp [r]
        ring
  have hexcessA : r * (1 + 7 * (p / Real.log D)) - 1 ≤
      A / Real.log D := by
    have hexact : r * (1 + 7 * (p / Real.log D)) - 1 =
        (3 * K + 7 * p) / Real.log D +
          21 * K * p * ((Real.log D)⁻¹ * (Real.log D)⁻¹) := by
      dsimp [r]
      field_simp [ne_of_gt hlog]
      ring
    have hcross :
        21 * K * p * ((Real.log D)⁻¹ * (Real.log D)⁻¹) ≤
          21 * K * p * (Real.log D)⁻¹ :=
      mul_le_mul_of_nonneg_left huu (by positivity)
    calc
      r * (1 + 7 * (p / Real.log D)) - 1 =
          (3 * K + 7 * p) / Real.log D +
            21 * K * p * ((Real.log D)⁻¹ * (Real.log D)⁻¹) := hexact
      _ ≤ (3 * K + 7 * p) / Real.log D +
            21 * K * p * (Real.log D)⁻¹ := add_le_add_right hcross _
      _ = A / Real.log D := by
        dsimp [A]
        rw [div_eq_mul_inv]
        ring
  have hcExcess : c * (r * (1 + 7 * (p / Real.log D)) - 1) ≤
      r * (1 + 7 * (p / Real.log D)) - 1 :=
    mul_le_of_le_one_left hexcess0 hc1
  have hraw : r * c * perturbation D d 0 3 - c ≤ A / Real.log D := by
    calc
      r * c * perturbation D d 0 3 - c ≤
          r * c * (1 + 7 * (p / Real.log D)) - c := sub_le_sub_right hmain c
      _ = c * (r * (1 + 7 * (p / Real.log D)) - 1) := by ring
      _ ≤ r * (1 + 7 * (p / Real.log D)) - 1 := hcExcess
      _ ≤ A / Real.log D := hexcessA
  have hinvpow : (Real.log D)⁻¹ ≤ (Real.log D) ^ (Δ - 1) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  have hAdec : A / Real.log D ≤ A * (Real.log D) ^ (Δ - 1) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinvpow hA0
  have htwodec := hdec D hDdecD
  have honeDec : A * (Real.log D) ^ (Δ - 1) ≤
      (1 - Δ) / (32 * sourceSigma D d) := by
    have hhalf := mul_le_mul_of_nonneg_left htwodec (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      A * (Real.log D) ^ (Δ - 1) =
          (1 / 2 : ℝ) * (2 * A * (Real.log D) ^ (Δ - 1)) := by ring
      _ ≤ (1 / 2 : ℝ) * ((1 - Δ) / (16 * sourceSigma D d)) := hhalf
      _ = (1 - Δ) / (32 * sourceSigma D d) := by ring
  simpa [r, c, sig] using hraw.trans (hAdec.trans honeDec)


end MathlibNt.SieveTheory
