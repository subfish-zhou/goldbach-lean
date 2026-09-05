import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13QhatMajorantInternal

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

open BridgeAssembly CutoffCorrectedRatio SourceClaim146AssemblyNext

private lemma shifted_slope_le_log
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d) (ht : 0 < t) :
    perturbationSlope D d 1 t ≤
      (d + 1) * Real.log (1 + (t + 1) ^ d / Real.log D) := by
  let u : ℝ := (t + 1) ^ d / Real.log D
  have htp : 0 < t + 1 := by linarith
  have hu0 : 0 ≤ u :=
    div_nonneg (Real.rpow_nonneg htp.le _) hlog.le
  have hb : 0 < 1 + u := by linarith
  have hulog : u / (1 + u) ≤ Real.log (1 + u) := by
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
    rw [Real.log_inv] at hi
    have heq : u / (1 + u) = 1 - (1 + u)⁻¹ := by
      field_simp [hb.ne']
      ring
    rw [heq]
    linarith
  have hpow : (t + 1) * (t + 1) ^ (d - 1) = (t + 1) ^ d := by
    calc
      (t + 1) * (t + 1) ^ (d - 1) =
          (t + 1) ^ (1 : ℝ) * (t + 1) ^ (d - 1) := by rw [Real.rpow_one]
      _ = (t + 1) ^ ((1 : ℝ) + (d - 1)) :=
        (Real.rpow_add htp _ _).symm
      _ = (t + 1) ^ d := by ring_nf
  have hnum :
      t * (d * (t + 1) ^ (d - 1) / Real.log D) ≤ d * u := by
    have hfac : 0 ≤ d * (t + 1) ^ (d - 1) / Real.log D :=
      div_nonneg (mul_nonneg hd (Real.rpow_nonneg htp.le _)) hlog.le
    calc
      t * (d * (t + 1) ^ (d - 1) / Real.log D) ≤
          (t + 1) * (d * (t + 1) ^ (d - 1) / Real.log D) := by
            exact mul_le_mul_of_nonneg_right (by linarith) hfac
      _ = d * u := by
        dsimp [u]
        rw [show (t + 1) * (d * (t + 1) ^ (d - 1) / Real.log D) =
          d * ((t + 1) * (t + 1) ^ (d - 1)) / Real.log D by ring, hpow]
        ring
  have hterm :
      t * (d * (t + 1) ^ (d - 1) / Real.log D) / (1 + u) ≤
        d * (u / (1 + u)) := by
    rw [show d * (u / (1 + u)) = (d * u) / (1 + u) by ring]
    exact (div_le_div_iff_of_pos_right hb).2 hnum
  rw [perturbationSlope]
  change Real.log (1 + u) +
      t * (d * (t + 1) ^ (d - 1) / Real.log D) / (1 + u) ≤ _
  calc
    Real.log (1 + u) +
        t * (d * (t + 1) ^ (d - 1) / Real.log D) / (1 + u) ≤
      Real.log (1 + u) + d * (u / (1 + u)) := add_le_add_right hterm _
    _ ≤ Real.log (1 + u) + d * Real.log (1 + u) := by gcongr
    _ = (d + 1) * Real.log (1 + u) := by ring

private lemma shifted_log_le_two_max
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (ht : 0 < t) (hdt : d ≤ t) :
    Real.log (1 + (t + 1) ^ d / Real.log D) ≤
      2 * max 1 (Real.log (1 + t ^ d / Real.log D)) := by
  let z : ℝ := t ^ d / Real.log D
  let r : ℝ := (t + 1) / t
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
  have hrpos : 0 < r := div_pos (by linarith) ht
  have hrone : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ ht).2
    linarith
  have hrform : r = 1 + 1 / t := by
    dsimp [r]
    field_simp [ne_of_gt ht]
  have hlogr : Real.log r ≤ 1 / t := by
    rw [hrform]
    have hp : 0 < 1 + 1 / t := by positivity
    linarith [Real.log_le_sub_one_of_pos hp]
  have hdtdiv : d / t ≤ 1 := (div_le_one ht).2 hdt
  have hdlog : d * Real.log r ≤ 1 := by
    have hd0 : 0 ≤ d := hd.le
    calc
      d * Real.log r ≤ d * (1 / t) := mul_le_mul_of_nonneg_left hlogr hd0
      _ = d / t := by ring
      _ ≤ 1 := hdtdiv
  have hrpow : r ^ d ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hrpos]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hdlog)
  have hpoweq : (t + 1) ^ d = t ^ d * r ^ d := by
    have htr : t * r = t + 1 := by
      dsimp [r]
      field_simp [ne_of_gt ht]
    rw [← Real.mul_rpow ht.le hrpos.le, htr]
  have hu : (t + 1) ^ d / Real.log D ≤ Real.exp 1 * z := by
    rw [hpoweq]
    dsimp [z]
    have htd0 : 0 ≤ t ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
    calc
      (t ^ d * r ^ d) / Real.log D = (t ^ d / Real.log D) * r ^ d := by ring
      _ ≤ (t ^ d / Real.log D) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hrpow htd0
      _ = Real.exp 1 * (t ^ d / Real.log D) := by ring
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase :
      1 + (t + 1) ^ d / Real.log D ≤ Real.exp 1 * (1 + z) := by
    calc
      1 + (t + 1) ^ d / Real.log D ≤ 1 + Real.exp 1 * z := by linarith
      _ ≤ Real.exp 1 + Real.exp 1 * z := by linarith
      _ = Real.exp 1 * (1 + z) := by ring
  have hleftpos : 0 < 1 + (t + 1) ^ d / Real.log D := by
    have : 0 ≤ (t + 1) ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ t + 1) _) hlog.le
    linarith
  have hlogcmp : Real.log (1 + (t + 1) ^ d / Real.log D) ≤
      1 + Real.log (1 + z) := by
    have hm := Real.strictMonoOn_log.monotoneOn hleftpos
      (mul_pos (Real.exp_pos 1) (by linarith : 0 < 1 + z)) hbase
    rw [Real.log_mul (Real.exp_ne_zero 1) (by linarith : 1 + z ≠ 0), Real.log_exp] at hm
    exact hm
  have hmax1 : 1 ≤ max 1 (Real.log (1 + z)) := le_max_left _ _
  have hmaxlog : Real.log (1 + z) ≤ max 1 (Real.log (1 + z)) := le_max_right _ _
  calc
    Real.log (1 + (t + 1) ^ d / Real.log D) ≤ 1 + Real.log (1 + z) := hlogcmp
    _ ≤ 2 * max 1 (Real.log (1 + z)) := by linarith
    _ = 2 * max 1 (Real.log (1 + t ^ d / Real.log D)) := by rfl

private lemma both_slopes_le_ratio_coefficient
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (ht : 0 < t) (hdt : d ≤ t) {ε : ℝ} (hε : ε = 0 ∨ ε = 1) :
    perturbationSlope D d ε t ≤
      2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) := by
  rcases hε with rfl | rfl
  · have hs : perturbationSlope D d 0 t ≤
        (d + 1) * Real.log (1 + t ^ d / Real.log D) := by
      -- The unshifted logarithmic derivative is the standard `z/(1+z)` estimate.
      let z : ℝ := t ^ d / Real.log D
      have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
      have hb : 0 < 1 + z := by linarith
      have hzlog : z / (1 + z) ≤ Real.log (1 + z) := by
        have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
        rw [Real.log_inv] at hi
        have heq : z / (1 + z) = 1 - (1 + z)⁻¹ := by
          field_simp [hb.ne']
          ring
        rw [heq]
        linarith
      have htpow : t * t ^ (d - 1) = t ^ d := by
        calc
          t * t ^ (d - 1) = t ^ (1 : ℝ) * t ^ (d - 1) := by rw [Real.rpow_one]
          _ = t ^ ((1 : ℝ) + (d - 1)) := (Real.rpow_add ht _ _).symm
          _ = t ^ d := by ring_nf
      have hterm : t * (d * t ^ (d - 1) / Real.log D) /
          (1 + t ^ d / Real.log D) = d * (z / (1 + z)) := by
        dsimp [z]
        rw [show t * (d * t ^ (d - 1) / Real.log D) =
          d * (t * t ^ (d - 1)) / Real.log D by ring, htpow]
        ring
      rw [perturbationSlope]
      simp only [add_zero]
      rw [hterm]
      calc
        Real.log (1 + z) + d * (z / (1 + z)) ≤
            Real.log (1 + z) + d * Real.log (1 + z) := by gcongr
        _ = (d + 1) * Real.log (1 + z) := by ring
    have hlogmax : Real.log (1 + t ^ d / Real.log D) ≤
        max 1 (Real.log (1 + t ^ d / Real.log D)) := le_max_right _ _
    have hd1 : 0 ≤ d + 1 := by linarith
    calc
      perturbationSlope D d 0 t ≤
          (d + 1) * Real.log (1 + t ^ d / Real.log D) := hs
      _ ≤ (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) :=
        mul_le_mul_of_nonneg_left hlogmax hd1
      _ ≤ 2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) := by
        have hm0 : 0 ≤ max 1 (Real.log (1 + t ^ d / Real.log D)) :=
          zero_le_one.trans (le_max_left _ _)
        nlinarith
  · have hs := shifted_slope_le_log hlog hd.le ht
    have hshift := shifted_log_le_two_max hlog hd ht hdt
    have hd1 : 0 ≤ d + 1 := by linarith
    calc
      perturbationSlope D d 1 t ≤
          (d + 1) * Real.log (1 + (t + 1) ^ d / Real.log D) := hs
      _ ≤ (d + 1) *
          (2 * max 1 (Real.log (1 + t ^ d / Real.log D))) :=
        mul_le_mul_of_nonneg_left hshift hd1
      _ = 2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) := by ring

/-- A single `Qhat` cutoff majorant and Proposition 13.1's delayed/current ratio
absorb the logarithmic derivatives for both `ε = 0` and `ε = 1`, uniformly on
the moving source range.  The proof splits at `(log D)^(1/d)` and keeps the
source upper bound in both branches. -/
theorem moving_derivativeDDE_largeRange_of_section13HatSourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d : ℝ} (hd : 0 < d)
    (Q : CutoffMajorant (section13Qhat H)) :
    ∃ M D₀ : ℝ, 1 < M ∧ 4 ≤ M ∧ 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      M ≤ sourceSigma D d ∧
      ∀ (sign : ErrorSign) (ε t : ℝ), (ε = 0 ∨ ε = 1) →
        M ≤ t → t ≤ sourceSigma D d →
        weightedHat H sign t * perturbationSlope D d ε t ≤
          t * H.T sign.opposite (t - 1) := by
  obtain ⟨M₀, hM₀, hratio₀⟩ :=
    exists_common_ratioOnSource_of_cutoffMajorants hH hd (fun _ => Q)
  let M : ℝ := max M₀ (max 4 d)
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hM1 : 1 < M := hM₀.trans_le hM₀M
  have hdM : d ≤ M := (le_max_right (4 : ℝ) d).trans (le_max_right M₀ _)
  have hratio : ∀ sign,
      Proposition131MovingDelayedCurrentRatioOnSource H sign d M := by
    intro sign
    exact proposition131MovingDelayedCurrentRatioOnSource_mono sign hd hM₀M
      (hratio₀ sign)
  obtain ⟨_, _, Dp, hDp, hratioD⟩ := hratio ErrorSign.plus
  obtain ⟨_, _, Dm, hDm, hratioDm⟩ := hratio ErrorSign.minus
  let D₀ : ℝ := max Dp Dm
  refine ⟨M, D₀, hM1, (le_max_left 4 d).trans (le_max_right M₀ _),
    hDp.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDpD : Dp ≤ D := (le_max_left Dp Dm).trans hD
  have hDmD : Dm ≤ D := (le_max_right Dp Dm).trans hD
  rcases hratioD D hDpD with ⟨hMσp, hp⟩
  rcases hratioDm D hDmD with ⟨hMσm, hm⟩
  refine ⟨hMσp, ?_⟩
  intro sign ε t hε hMt htσ
  have hD1 : 1 < D := hDp.trans_le hDpD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have ht : 0 < t := (zero_lt_one.trans hM1).trans_le hMt
  have hdt : d ≤ t := hdM.trans hMt
  have hW0 : 0 ≤ weightedHat H sign t := by
    exact mul_nonneg (sq_nonneg t) (hH.toSection13HatContract.positive sign t ht).le
  have hslope := both_slopes_le_ratio_coefficient hlog hd ht hdt hε
  have hmul : weightedHat H sign t * perturbationSlope D d ε t ≤
      2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) *
        weightedHat H sign t := by
    calc
      weightedHat H sign t * perturbationSlope D d ε t ≤
          weightedHat H sign t *
            (2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D))) :=
        mul_le_mul_of_nonneg_left hslope hW0
      _ = 2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) *
          weightedHat H sign t := by ring
  by_cases hcut : t ≤ (Real.log D) ^ (1 / d)
  · -- Proposition 13.1, lower source range.
    cases sign with
    | plus => exact hmul.trans (hp t hMt htσ)
    | minus => exact hmul.trans (hm t hMt htσ)
  · -- Proposition 13.1, upper source range; `htσ` is retained explicitly.
    have _habove : (Real.log D) ^ (1 / d) < t := lt_of_not_ge hcut
    cases sign with
    | plus => exact hmul.trans (hp t hMt htσ)
    | minus => exact hmul.trans (hm t hMt htσ)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
