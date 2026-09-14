import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection10CutoffCorrectedRatio
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingCertificateOnSource
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131TailDecay
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaClaim146SourceAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDDEAsymptoticClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFixedGapRpowMargin
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaElementaryHead

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

open BridgeAssembly CutoffCorrectedRatio SourceClaim146AssemblyNext

def SourceCutoffLogDomination
    (K A d M : ℝ) : Prop :=
  0 < d ∧ 1 < M ∧
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    M ≤ sourceSigma D d ∧ ∀ t : ℝ, M ≤ t → t ≤ sourceSigma D d →
      2 * (d + 1) * K ^ 2 * A *
          max 1 (Real.log (1 + t ^ d / Real.log D)) ≤
        Real.log (Real.exp 1 * t)

private lemma source_bridge_Qhat_rfl
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) :
    (section13_bridgeAtThree hH sign).Qhat = section13Qhat H := rfl

private lemma source_bridge_K_opposite_rfl
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) :
    (section13_bridgeAtThree hH sign.opposite).K =
      (section13_bridgeAtThree hH sign).K := rfl

private lemma max_one_le_one_add (x : ℝ) (hx0 : 0 ≤ x) :
    max 1 x ≤ 1 + x := by
  by_cases hx : x ≤ 1
  · rw [max_eq_left hx]
    linarith
  · rw [max_eq_right (le_of_not_ge hx)]
    linarith

private lemma source_cutoff_case_one_bound
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (ht : 0 < t) (hcut : t ≤ (Real.log D) ^ (1 / d)) :
    t ^ d / Real.log D ≤ 1 := by
  exact moving_below_cutoff_z_le_one hlog hd ht hcut

theorem exists_sourceCutoffLogDomination
    {K A d : ℝ} (hd : 0 < d) (hK : 1 ≤ K) (hA : 1 ≤ A) :
    ∃ M : ℝ, SourceCutoffLogDomination K A d M := by
  let C := 2 * (d + 1) * K ^ 2 * A
  have hC : 0 < C := by dsimp [C]; positivity
  let e := min (d / 2) (1 / (4 * C))
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have hed : e < d := (min_le_left _ _).trans_lt (by linarith)
  have heC : C * e ≤ 1 / 4 := by
    calc
      C * e ≤ C * (1 / (4 * C)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = 1 / 4 := by field_simp
  let q := d - e
  have hq : 0 < q := sub_pos.mpr hed
  let r := 1 / q - 1 / d
  have hr : 0 < r := by
    dsimp [r]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hq (by dsimp [q]; linarith))
  let X := max 2 (max (Real.log 27) ((4 / r) ^ (1 / (r / 2))))
  let M := Real.exp (4 * C + 1)
  have hM : 1 < M := Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨D₁, hD₁, hlower⟩ := exists_sourceSigma_fixed_lower_threshold d M hd.le
  refine ⟨M, hd, hM, max D₁ (Real.exp X), hD₁.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  refine ⟨hlower D ((le_max_left _ _).trans hD), ?_⟩
  have hDX : Real.exp X ≤ D := (le_max_right _ _).trans hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hDX
  have hX : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).mpr hDX
  let x := Real.log D
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hX
  have hx : 0 < x := by linarith
  have hx27 : Real.log 27 ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hxroot : (4 / r) ^ (1 / (r / 2)) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hxpow : 4 / r ≤ x ^ (r / 2) := by
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) hx.le (by positivity)).mp
    simpa only [one_div] using hxroot
  -- A positive power absorbs the iterated logarithm at the actual source cutoff.
  have hlog : 2 * Real.log x ≤ x ^ r := by
    calc
      2 * Real.log x ≤ 2 * (x ^ (r / 2) / (r / 2)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx.le (by positivity)) (by norm_num)
      _ = (4 / r) * x ^ (r / 2) := by ring
      _ ≤ x ^ (r / 2) * x ^ (r / 2) :=
        mul_le_mul_of_nonneg_right hxpow (Real.rpow_nonneg hx.le _)
      _ = x ^ r := by rw [← Real.rpow_add hx]; congr 1; ring
  have hinner : Real.log (27 * D) = Real.log 27 + x :=
    Real.log_mul (by norm_num) hDpos.ne'
  have hinnerpos : 0 < Real.log (27 * D) := by
    rw [hinner]
    exact add_pos (Real.log_pos (by norm_num)) hx
  have hll : Real.log (Real.log (27 * D)) ≤ x ^ r := by
    calc
      Real.log (Real.log (27 * D)) ≤ Real.log (2 * x) :=
        Real.log_le_log hinnerpos (by rw [hinner]; linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx.ne'
      _ ≤ 2 * Real.log x := by
        have := Real.log_le_log (by norm_num : (0:ℝ) < 2) hx2
        linarith
      _ ≤ x ^ r := hlog
  have hsigma : sourceSigma D d ≤ x ^ (1 / q) := by
    calc
      sourceSigma D d ≤ x ^ (1 / d) * x ^ r := by
        simpa only [sourceSigma] using
          mul_le_mul_of_nonneg_left hll (Real.rpow_nonneg hx.le _)
      _ = x ^ (1 / q) := by
        rw [← Real.rpow_add hx]
        congr 1
        dsimp [r]
        ring
  intro t ht hts
  have ht1 : 1 < t := hM.trans_le ht
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlt : 4 * C + 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ht
  have hlogt : 0 ≤ Real.log t := (Real.log_pos ht1).le
  have htpow : t ^ q ≤ x := by
    have := Real.rpow_le_rpow ht0.le (hts.trans hsigma) hq.le
    simpa only [← Real.rpow_mul hx.le, one_div_mul_cancel hq.ne', Real.rpow_one] using this
  have hratio : t ^ d / Real.log D ≤ t ^ e := by
    apply (div_le_iff₀ hx).mpr
    calc
      t ^ d = t ^ e * t ^ q := by
        rw [← Real.rpow_add ht0]
        congr 1
        dsimp [q]
        ring
      _ ≤ t ^ e * x := mul_le_mul_of_nonneg_left htpow (Real.rpow_nonneg ht0.le _)
  have hte : 1 ≤ t ^ e := Real.one_le_rpow ht1.le he.le
  have hlogratio : Real.log (1 + t ^ d / Real.log D) ≤ Real.log 2 + e * Real.log t := by
    calc
      Real.log (1 + t ^ d / Real.log D) ≤ Real.log (2 * t ^ e) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + e * Real.log t := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos ht0 e).ne', Real.log_rpow ht0]
  have hC1 : C ≤ Real.log t := by linarith only [hlt, hC]
  have hClog : C * Real.log (1 + t ^ d / Real.log D) ≤ Real.log t := by
    have hce := mul_le_mul_of_nonneg_right heC hlogt
    have hcb := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)) hC.le
    have hmain := mul_le_mul_of_nonneg_left hlogratio hC.le
    linarith only [hce, hcb, hmain, hlt, hlogt]
  change C * max 1 (Real.log (1 + t ^ d / Real.log D)) ≤ _
  rw [mul_max_of_nonneg _ _ hC.le, mul_one]
  have hmax := max_le hC1 hClog
  rw [Real.log_mul (Real.exp_ne_zero 1) ht0.ne', Real.log_exp]
  exact hmax.trans (le_add_of_nonneg_left zero_le_one)

private lemma slope_le_log
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d) (ht : 0 < t) :
    perturbationSlope D d 0 t ≤
      (d + 1) * Real.log (1 + t ^ d / Real.log D) := by
  exact moving_perturbationSlope_le_log hlog hd ht

private lemma above_cutoff_one_lt_z
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (hcut : (Real.log D) ^ (1 / d) < t) :
    1 < t ^ d / Real.log D := by
  exact moving_above_cutoff_one_lt_z hlog hd hcut

theorem proposition131MovingDelayedCurrentRatioOnSource_mono
    {H : Section13HatLayers} (sign : ErrorSign) {d M₀ M : ℝ} (hd : 0 < d)
    (hM : M₀ ≤ M)
    (hratio : Proposition131MovingDelayedCurrentRatioOnSource H sign d M₀) :
    Proposition131MovingDelayedCurrentRatioOnSource H sign d M := by
  rcases hratio with ⟨hd', hM₀1, D₀, hD₀, hratio⟩
  obtain ⟨Ds, hDs, hsource⟩ :=
    exists_sourceSigma_fixed_lower_threshold d M hd.le
  refine ⟨hd', lt_of_lt_of_le hM₀1 hM, max D₀ Ds, hD₀.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hD₀D : D₀ ≤ D := (le_max_left D₀ Ds).trans hD
  have hDsD : Ds ≤ D := (le_max_right D₀ Ds).trans hD
  rcases hratio D hD₀D with ⟨hM₀σ, hratioD⟩
  refine ⟨hsource D hDsD, ?_⟩
  intro t hMt htσ
  exact hratioD t (hM.trans hMt) htσ

theorem exists_ratioOnSource_of_cutoffMajorant
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {d : ℝ} (hd : 0 < d)
    (majorant : CutoffMajorant (section13_bridgeAtThree hH sign).Qhat) :
    ∃ M : ℝ, Proposition131MovingDelayedCurrentRatioOnSource H sign d M := by
  let B := section13_bridgeAtThree hH sign
  let Bopp := section13_bridgeAtThree hH sign.opposite
  obtain ⟨Mlog, hlog⟩ :=
    exists_sourceCutoffLogDomination hd B.one_le_K majorant.one_le_A
  rcases hlog with ⟨_, hMlog, Dlog, hDlog, hlogD⟩
  let M : ℝ := max majorant.cutoff Mlog
  obtain ⟨Ds, hDs, hsource⟩ :=
    exists_sourceSigma_fixed_lower_threshold d M hd.le
  let D₀ : ℝ := max Dlog Ds
  have hM1 : 1 < M := lt_of_lt_of_le hMlog (le_max_right _ _)
  refine ⟨M, hd, hM1, D₀, hDlog.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDlogD : Dlog ≤ D := (le_max_left Dlog Ds).trans hD
  have hDsD : Ds ≤ D := (le_max_right Dlog Ds).trans hD
  refine ⟨hsource D hDsD, ?_⟩
  intro t hMt htσ
  rcases hlogD D hDlogD with ⟨_, hlogt⟩
  have hcut : majorant.cutoff ≤ t := (le_max_left _ _).trans hMt
  have hMlogt : Mlog ≤ t := (le_max_right _ _).trans hMt
  have ht3 : 3 ≤ t := by
    linarith [majorant.four_le_cutoff, hcut]
  have htm13 : 3 ≤ t - 1 := by
    nlinarith [majorant.four_le_cutoff, hcut]
  have ht0 : 0 < t := by linarith
  have hloget : 0 < Real.log (Real.exp 1 * t) := by
    have ht1 : 1 ≤ t := by linarith
    have htne : t ≠ 0 := ne_of_gt ht0
    rw [Real.log_mul (Real.exp_ne_zero 1) htne, Real.log_exp]
    linarith [Real.log_nonneg ht1]
  have hTopp0 : 0 ≤ H.T sign.opposite (t - 1) := by
    exact (hH.toSection13HatContract.positive sign.opposite (t - 1) (by linarith)).le
  have hratioT :
      H.T sign t ≤
        (B.K ^ 2 * majorant.A) / (t * Real.log (Real.exp 1 * t)) *
          H.T sign.opposite (t - 1) := by
    calc
      H.T sign t ≤ B.K * B.Qhat t := B.hat_le t ht3
      _ ≤ B.K *
            (majorant.A / (t * Real.log (Real.exp 1 * t)) * B.Qhat (t - 1)) := by
              exact mul_le_mul_of_nonneg_left
                (section10_unitShift_after_cutoff B.dde majorant hcut)
                (zero_le_one.trans B.one_le_K)
      _ ≤ B.K *
            (majorant.A / (t * Real.log (Real.exp 1 * t)) *
              (Bopp.K * H.T sign.opposite (t - 1))) := by
              apply mul_le_mul_of_nonneg_left
              exact mul_le_mul_of_nonneg_left
                (Bopp.Q_le (t - 1) htm13)
                (div_nonneg (zero_le_one.trans majorant.one_le_A)
                  (mul_nonneg ht0.le hloget.le))
              exact zero_le_one.trans B.one_le_K
      _ =
          (B.K ^ 2 * majorant.A) / (t * Real.log (Real.exp 1 * t)) *
            H.T sign.opposite (t - 1) := by
              rw [source_bridge_K_opposite_rfl hH sign]
              ring
  have hWbound :
      weightedHat H sign t ≤
        ((B.K ^ 2 * majorant.A) / Real.log (Real.exp 1 * t)) *
          (t * H.T sign.opposite (t - 1)) := by
    calc
      weightedHat H sign t =
          t ^ 2 * H.T sign t := by rfl
      _ ≤ t ^ 2 *
            (((B.K ^ 2 * majorant.A) / (t * Real.log (Real.exp 1 * t))) *
              H.T sign.opposite (t - 1)) := by
              exact mul_le_mul_of_nonneg_left hratioT (sq_nonneg t)
      _ =
          ((B.K ^ 2 * majorant.A) / Real.log (Real.exp 1 * t)) *
            (t * H.T sign.opposite (t - 1)) := by
              field_simp [ne_of_gt ht0, ne_of_gt hloget]
  have hcoef0 :
      0 ≤ 2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) := by
    have : 0 ≤ max 1 (Real.log (1 + t ^ d / Real.log D)) := by
      linarith [le_max_left (1 : ℝ) (Real.log (1 + t ^ d / Real.log D))]
    nlinarith
  have hlogcoef :
      (2 * (d + 1) * B.K ^ 2 * majorant.A *
          max 1 (Real.log (1 + t ^ d / Real.log D))) /
        Real.log (Real.exp 1 * t) ≤ 1 := by
    apply (div_le_iff₀ hloget).2
    simpa using hlogt t hMlogt htσ
  calc
    2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) *
        weightedHat H sign t
        ≤
          2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) *
            (((B.K ^ 2 * majorant.A) / Real.log (Real.exp 1 * t)) *
              (t * H.T sign.opposite (t - 1))) := by
                exact mul_le_mul_of_nonneg_left hWbound hcoef0
    _ =
        (((2 * (d + 1) * B.K ^ 2 * majorant.A *
              max 1 (Real.log (1 + t ^ d / Real.log D))) /
            Real.log (Real.exp 1 * t))) *
          (t * H.T sign.opposite (t - 1)) := by ring
    _ ≤ 1 * (t * H.T sign.opposite (t - 1)) := by
      exact mul_le_mul_of_nonneg_right hlogcoef (mul_nonneg ht0.le hTopp0)
    _ = t * H.T sign.opposite (t - 1) := by ring

theorem exists_common_ratioOnSource_of_cutoffMajorants
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d : ℝ} (hd : 0 < d)
    (majorant : ∀ sign, CutoffMajorant (section13_bridgeAtThree hH sign).Qhat) :
    ∃ M : ℝ, 1 < M ∧ ∀ sign,
      Proposition131MovingDelayedCurrentRatioOnSource H sign d M := by
  obtain ⟨Mplus, hplus⟩ :=
    exists_ratioOnSource_of_cutoffMajorant hH ErrorSign.plus hd (majorant ErrorSign.plus)
  obtain ⟨Mminus, hminus⟩ :=
    exists_ratioOnSource_of_cutoffMajorant hH ErrorSign.minus hd (majorant ErrorSign.minus)
  let M : ℝ := max Mplus Mminus
  have hM1 : 1 < M := by
    rcases hplus with ⟨_, hplus1, _⟩
    exact lt_of_lt_of_le hplus1 (le_max_left _ _)
  refine ⟨M, hM1, ?_⟩
  intro sign
  cases sign with
  | plus =>
      exact proposition131MovingDelayedCurrentRatioOnSource_mono ErrorSign.plus hd
        (le_max_left _ _) hplus
  | minus =>
      exact proposition131MovingDelayedCurrentRatioOnSource_mono ErrorSign.minus hd
        (le_max_right _ _) hminus

private noncomputable def lambdaNegDerivStrict
    (H : Section13HatLayers) (sign : ErrorSign) (D d t : ℝ) : ℝ :=
  perturbation D d 0 t *
    (t * H.T sign.opposite (t - 1) -
      weightedHat H sign t * perturbationSlope D d 0 t)

private lemma hasDerivAt_lambdaNegStrict
    {H : Section13HatLayers} {β D d t : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht0 : 0 < t)
    (ht : β + sign.epsilon < t) :
    HasDerivAt (-lambda H sign D d 0)
      (lambdaNegDerivStrict H sign D d t) t := by
  have h := (hasDerivAt_lambda_of_contract (d := d) hH sign hlog
    (show 0 < t + 0 by linarith) ht).neg
  have heq : lambdaNegDerivStrict H sign D d t =
      -(perturbation D d 0 t *
        (weightedHat H sign t * perturbationSlope D d 0 t -
          t * H.T sign.opposite (t - 1))) := by
    unfold lambdaNegDerivStrict
    ring
  rw [heq]
  simpa only [Pi.neg_apply, perturbationSlope] using h

private lemma qD_eq_dde_mainStrict
    {H : Section13HatLayers} {D d Δ t : ℝ} (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht : 1 < t) :
    qD H sign.opposite D d Δ t =
      (perturbation D d 0 t * (t * H.T sign.opposite (t - 1)) /
          (1 + t ^ d / Real.log D)) *
        ((t - 1) / t) ^ (1 - Δ) := by
  exact qD_eq_dde_main sign hlog ht

private lemma qD_le_lambdaNegDeriv_mul_weightStrict
    {H : Section13HatLayers} {β D d Δ t : ℝ}
    (_hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht : 1 < t)
    (hasymp : weightedHat H sign t * perturbationSlope D d 0 t ≤
      t * H.T sign.opposite (t - 1) *
        ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D))) :
    qD H sign.opposite D d Δ t ≤
      lambdaNegDerivStrict H sign D d t * ((t - 1) / t) ^ (1 - Δ) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  let z : ℝ := t ^ d / Real.log D
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht0.le _) hlog.le
  have hb : 0 < 1 + z := by linarith
  have hmain : t * H.T sign.opposite (t - 1) / (1 + z) ≤
      t * H.T sign.opposite (t - 1) -
        weightedHat H sign t * perturbationSlope D d 0 t := by
    dsimp [z] at hasymp ⊢
    calc
      t * H.T sign.opposite (t - 1) / (1 + t ^ d / Real.log D) =
          t * H.T sign.opposite (t - 1) -
            t * H.T sign.opposite (t - 1) *
              ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
            field_simp [hb.ne']
            ring
      _ ≤ t * H.T sign.opposite (t - 1) -
            weightedHat H sign t * perturbationSlope D d 0 t := by
              exact sub_le_sub_left hasymp _
  have hp0 : 0 ≤ perturbation D d 0 t := by
    rw [perturbation]
    simpa [z] using Real.rpow_nonneg hb.le t
  have hw0 : 0 ≤ ((t - 1) / t) ^ (1 - Δ) :=
    Real.rpow_nonneg (div_pos (sub_pos.mpr ht) ht0).le _
  rw [qD_eq_dde_mainStrict sign hlog ht]
  dsimp [lambdaNegDerivStrict]
  apply mul_le_mul_of_nonneg_right _ hw0
  convert mul_le_mul_of_nonneg_left hmain hp0 using 1; ring

private lemma continuousOn_lambdaNegDerivStrict
    {H : Section13HatLayers} {β D d a b : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ha : β + sign.epsilon < a) :
    ContinuousOn (lambdaNegDerivStrict H sign D d) (Icc a b) := by
  have heps : 0 ≤ sign.epsilon := by
    cases sign <;> simp [ErrorSign.epsilon]
  have ha0 : 0 < a := by linarith [hH.beta_gt_one]
  have hp : ContinuousOn (perturbation D d 0) (Icc a b) := by
    intro t ht
    exact (hasDerivAt_perturbation (d := d) hlog
      (by simpa using ha0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hT : ContinuousOn (fun t => t * H.T sign.opposite (t - 1)) (Icc a b) :=
    continuousOn_id.mul ((hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const) (by
        intro t ht
        have : 1 < t := by linarith [hH.beta_gt_one, heps, ha, ht.1]
        exact sub_pos.mpr this))
  have hw : ContinuousOn (weightedHat H sign) (Icc a b) :=
    (continuousOn_id.pow 2).mul ((hH.continuous sign).mono (by
      intro t ht
      exact ha0.trans_le ht.1))
  have hs : ContinuousOn (perturbationSlope D d 0) (Icc a b) := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hden : 0 < 1 + (t + 0) ^ d / Real.log D := by
      have : 0 ≤ (t + 0) ^ d / Real.log D :=
        div_nonneg (by simpa [add_zero] using Real.rpow_nonneg (ha0.trans_le ht.1).le d) hlog.le
      linarith
    unfold perturbationSlope
    fun_prop (disch := aesop)
  exact hp.mul (hT.sub (hw.mul hs))

private lemma continuousOn_qD_tailStrict
    {H : Section13HatLayers} {β D d Δ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hs : 1 < s) :
    ContinuousOn (qD H sign D d Δ) (Icc s σ) := by
  exact continuousOn_qD_Icc_of_contract hH sign hD hs

theorem eventually_movingSigma_large_s_differential_tail_onSource_strict
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {d Δ M : ℝ}
    (hM : 4 ≤ M) (hΔ : Δ < 1)
    (hcert : MovingDDEAsymptoticCertificateOnSource H sign d M) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      M ≤ sourceSigma D d ∧
      ∀ s : ℝ, M ≤ s → s ≤ sourceSigma D d →
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            lambda H sign D d 0 s := by
  rcases hcert with ⟨D₀, hD₀, hcert⟩
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  rcases hcert D hD with ⟨hMσ, hlo, hhi⟩
  refine ⟨hMσ, ?_⟩
  intro s hs hssigma
  let σ := sourceSigma D d
  have hD1 : 1 < D := hD₀.trans_le hD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hs2 : 2 < s := by linarith
  have hs0 : 0 < s := by linarith
  have hσ2 : 2 < σ := hs2.trans_le hssigma
  have hσ0 : 0 < σ := by linarith
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  have hc0 : 0 < c := by
    apply Real.rpow_pos_of_pos
    exact sub_pos.mpr ((div_lt_one hσ0).mpr (by linarith : 1 < σ))
  have hp : 0 < 1 - Δ := sub_pos.mpr hΔ
  have hweight : ∀ t ∈ Icc s σ,
      ((t - 1) / t) ^ (1 - Δ) ≤ c := by
    intro t ht
    have ht0 : 0 < t := hs0.trans_le ht.1
    have ht1 : 1 < t := by linarith [hs2, ht.1]
    have hb0 : 0 ≤ (t - 1) / t := (div_pos (sub_pos.mpr ht1) ht0).le
    have hinv : 1 / σ ≤ 1 / t := one_div_le_one_div_of_le ht0 ht.2
    have hbase : (t - 1) / t ≤ 1 - 1 / σ := by
      calc
        (t - 1) / t = 1 - 1 / t := by field_simp [ne_of_gt ht0]
        _ ≤ 1 - 1 / σ := sub_le_sub_left hinv 1
    dsimp [c]
    exact Real.rpow_le_rpow hb0 hbase hp.le
  have hasymp : ∀ t ∈ Icc s σ,
      weightedHat H sign t * perturbationSlope D d 0 t ≤
        t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
    intro t ht
    by_cases hr : t ≤ (Real.log D) ^ (1 / d)
    · exact hlo t (hs.trans ht.1) hr ht.2
    · exact hhi t (lt_of_not_ge hr) ht.2
  have hpoint : ∀ t ∈ Icc s σ,
      qD H sign.opposite D d Δ t ≤
        c * lambdaNegDerivStrict H sign D d t := by
    intro t ht
    have ht1 : 1 < t := by linarith [hs2, ht.1]
    have hd0 :=
      qD_le_lambdaNegDeriv_mul_weightStrict (Δ := Δ) hH sign hlog ht1 (hasymp t ht)
    have hneg0 : 0 ≤ lambdaNegDerivStrict H sign D d t := by
      have hp0 : 0 ≤ perturbation D d 0 t := by
        rw [perturbation]
        apply Real.rpow_nonneg
        have : 0 ≤ t ^ d / Real.log D :=
          div_nonneg (Real.rpow_nonneg (by linarith) _) hlog.le
        have : 0 ≤ (t + 0) ^ d / Real.log D := by simpa using this
        linarith
      unfold lambdaNegDerivStrict
      apply mul_nonneg hp0
      have hzfrac : (t ^ d / Real.log D) / (1 + t ^ d / Real.log D) ≤ 1 := by
        apply (div_le_one (by
          have : 0 ≤ t ^ d / Real.log D :=
            div_nonneg (Real.rpow_nonneg (by linarith) _) hlog.le
          linarith)).2
        linarith
      have hmain0 : 0 ≤ t * H.T sign.opposite (t - 1) :=
        (mul_pos (by linarith)
          (hH.positive sign.opposite (t - 1) (by linarith))).le
      rw [sub_nonneg]
      calc
        weightedHat H sign t * perturbationSlope D d 0 t ≤
            t * H.T sign.opposite (t - 1) *
              ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := hasymp t ht
        _ ≤ t * H.T sign.opposite (t - 1) := by
          exact mul_le_of_le_one_right hmain0 hzfrac
    exact hd0.trans (by
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left (hweight t ht) hneg0)
  have hqcont : ContinuousOn (qD H sign.opposite D d Δ) (Icc s σ) :=
    continuousOn_qD_tailStrict hH sign.opposite hD1 (by linarith)
  have hdcont : ContinuousOn (lambdaNegDerivStrict H sign D d) (Icc s σ) :=
    continuousOn_lambdaNegDerivStrict (a := s) (b := σ) hH sign hlog (by
      cases sign <;> simp [ErrorSign.epsilon] <;> linarith [hs2])
  have hmono : (∫ t in s..σ, qD H sign.opposite D d Δ t) ≤
      ∫ t in s..σ, c * lambdaNegDerivStrict H sign D d t := by
    exact intervalIntegral.integral_mono_on hssigma
      (hqcont.intervalIntegrable_of_Icc hssigma)
      ((continuousOn_const.mul hdcont).intervalIntegrable_of_Icc hssigma) hpoint
  have hFTC : (∫ t in s..σ, lambdaNegDerivStrict H sign D d t) =
      lambda H sign D d 0 s - lambda H sign D d 0 σ := by
    have hderiv : ∀ t ∈ Ioo s σ,
        HasDerivAt (-lambda H sign D d 0)
          (lambdaNegDerivStrict H sign D d t) t := by
      intro t ht
      apply hasDerivAt_lambdaNegStrict hH sign hlog (by linarith [hs0, ht.1])
      cases sign <;> simp [ErrorSign.epsilon] <;> linarith [hs2, ht.1]
    have hfcont : ContinuousOn (-lambda H sign D d 0) (Icc s σ) := by
      intro t ht
      exact (hasDerivAt_lambdaNegStrict hH sign hlog (by linarith [hs0, ht.1]) (by
        cases sign <;> simp [ErrorSign.epsilon] <;> linarith [hs2, ht.1])).continuousAt.continuousWithinAt
    have hraw := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hssigma
      hfcont hderiv (hdcont.intervalIntegrable_of_Icc hssigma)
    simpa [σ, lambda_eq_perturb_mul_weightedHat, perturbation, sub_eq_add_neg,
      add_comm] using hraw
  have hlamσ : 0 < lambda H sign D d 0 σ := by
    exact lambda_pos H sign hD1 (by norm_num) hσ0 (hH.positive sign σ hσ0)
  calc
    (∫ t in s..σ, qD H sign.opposite D d Δ t) ≤
        ∫ t in s..σ, c * lambdaNegDerivStrict H sign D d t := hmono
    _ = c * (lambda H sign D d 0 s - lambda H sign D d 0 σ) := by
      rw [intervalIntegral.integral_const_mul, hFTC]
    _ < c * lambda H sign D d 0 s := by
      nlinarith [hc0, hlamσ]
    _ = (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          lambda H sign D d 0 s := by
            rfl

private lemma qD_split_at_fixed_source_point
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {D d Δ M s : ℝ} (hD : 1 < D)
    (hs : 2 + sign.epsilon ≤ s) (hsM : s ≤ M)
    (hMσ : M + 2 ≤ sourceSigma D d) :
    (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) =
      (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
      (∫ t in M + 2..sourceSigma D d, qD H sign.opposite D d Δ t) := by
  have hs1 : 1 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs ⊢ <;> linarith
  have hcont : ContinuousOn (qD H sign.opposite D d Δ)
      (Icc s (sourceSigma D d)) :=
    continuousOn_qD_Icc_of_contract hH sign.opposite hD hs1
  have hintLeft :
      IntervalIntegrable (qD H sign.opposite D d Δ) volume s (M + 2) :=
    (hcont.mono (Icc_subset_Icc_right hMσ)).intervalIntegrable_of_Icc (by linarith)
  have hintRight :
      IntervalIntegrable (qD H sign.opposite D d Δ) volume (M + 2) (sourceSigma D d) :=
    (hcont.mono (Icc_subset_Icc_left (by linarith : s ≤ M + 2))).intervalIntegrable_of_Icc hMσ
  exact (intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight).symm

private lemma claim146iii_margin_of_le
    {C gap M : ℝ} (hC : 0 ≤ C) (hgap : 0 < gap)
    (hM : claim146iiiFixedM C gap ≤ M) :
    4 ≤ M ∧ 2 * C / M ^ 2 < gap / (4 * M) := by
  have hM4 : 4 ≤ M := (le_max_left 4 (16 * C / gap + 1)).trans hM
  have hMpos : 0 < M := by linarith
  have hMlower : 16 * C / gap + 1 ≤ M := (le_max_right 4 (16 * C / gap + 1)).trans hM
  have hcross : 16 * C < gap * M := by
    have hscaled := mul_le_mul_of_nonneg_left hMlower hgap.le
    have hident : gap * (16 * C / gap + 1) = 16 * C + gap := by
      field_simp [ne_of_gt hgap]
    rw [hident] at hscaled
    linarith
  refine ⟨hM4, ?_⟩
  rw [div_lt_div_iff₀ (sq_pos_of_pos hMpos) (mul_pos (by norm_num) hMpos)]
  nlinarith [sq_nonneg M]

theorem moving_claim14_6_iii_of_source_contract_and_cutoffMajorants
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d Δ : ℝ} (hd : 0 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (majorant : ∀ sign,
      CutoffMajorant (section13_bridgeAtThree hH sign).Qhat) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ (sign : ErrorSign) (s : ℝ),
        2 + sign.epsilon ≤ s → s ≤ sourceSigma D d →
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            lambda H sign D d 0 s := by
  let hAsymp :=
    CutoffCorrectedRatio.section13HatAsymptoticContract_of_atThree_cutoff
      hH.toSection13HatContract (section13_bridgeAtThree hH) majorant
  let h131 :=
    section13HatAsymptoticContract_implies_proposition131TailDecay
      hH.toSection13HatContract hAsymp
  obtain ⟨C, hC, h131C⟩ := h131
  let gap : ℝ := 1 - Δ
  have hgap : 0 < gap := sub_pos.mpr hΔ1
  obtain ⟨Mratio, hMratio1, hratioBase⟩ :=
    exists_common_ratioOnSource_of_cutoffMajorants hH hd majorant
  let Mcore : ℝ := claim146iiiFixedM C gap
  let M : ℝ := max Mcore Mratio
  have hMMcore : Mcore ≤ M := le_max_left _ _
  have hMMratio : Mratio ≤ M := le_max_right _ _
  have hM4 : 4 ≤ M := (claim146iii_margin_of_le hC hgap hMMcore).1
  have hcoef : 2 * C / M ^ 2 < gap / (4 * M) :=
    (claim146iii_margin_of_le hC hgap hMMcore).2
  have hratio : ∀ sign, Proposition131MovingDelayedCurrentRatioOnSource H sign d M := by
    intro sign
    exact proposition131MovingDelayedCurrentRatioOnSource_mono sign hd hMMratio
      (hratioBase sign)
  obtain ⟨Dp, hDp, hpert⟩ :=
    fixedCompactPerturbationContract (d := d) (M := M) hd.le hM4
  obtain ⟨Dh, hDh, hhead⟩ :=
    lemma133WeightedHeadContract_corrected hH.toSection13HatContract
      (d := d) (Δ := Δ) (M := M) hd.le hΔ0 hΔ1 hM4
  obtain ⟨DtPlus, hDtPlus, htailPlus⟩ :=
    eventually_movingSigma_large_s_differential_tail_onSource_strict
      hH.toSection13HatContract ErrorSign.plus hM4 hΔ1
      (movingDDEAsymptoticCertificateOnSource_of_proposition131_ratioOnSource
        hH.toSection13HatContract ErrorSign.plus (hratio ErrorSign.plus))
  obtain ⟨DtMinus, hDtMinus, htailMinus⟩ :=
    eventually_movingSigma_large_s_differential_tail_onSource_strict
      hH.toSection13HatContract ErrorSign.minus hM4 hΔ1
      (movingDDEAsymptoticCertificateOnSource_of_proposition131_ratioOnSource
        hH.toSection13HatContract ErrorSign.minus (hratio ErrorSign.minus))
  obtain ⟨Dσ, hDσ, hsourceσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold d (M + 2) hd.le
  let D₀ : ℝ := max Dp (max Dh (max DtPlus (max DtMinus Dσ)))
  refine ⟨D₀, hDp.trans_le (le_max_left _ _), ?_⟩
  intro D hD sign s hs hsσ
  have hDpD : Dp ≤ D := (le_max_left Dp _).trans hD
  have hDhD : Dh ≤ D :=
    (le_max_left Dh _).trans ((le_max_right Dp _).trans hD)
  have hDtPlusD : DtPlus ≤ D :=
    (le_max_left DtPlus _).trans ((le_max_right Dh _).trans ((le_max_right Dp _).trans hD))
  have hDtMinusD : DtMinus ≤ D := by
    exact (le_max_left DtMinus Dσ).trans
      ((le_max_right DtPlus (max DtMinus Dσ)).trans
        ((le_max_right Dh _).trans ((le_max_right Dp _).trans hD)))
  have hDσD : Dσ ≤ D := by
    exact (le_max_right DtMinus Dσ).trans
      ((le_max_right DtPlus (max DtMinus Dσ)).trans
        ((le_max_right Dh _).trans ((le_max_right Dp _).trans hD)))
  have hD1 : 1 < D := hDp.trans_le hDpD
  have hM2σ : M + 2 ≤ sourceSigma D d := hsourceσ D hDσD
  have hlarge :
      ∀ sign : ErrorSign, ∀ s : ℝ, M ≤ s → s ≤ sourceSigma D d →
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            lambda H sign D d 0 s := by
    intro sign s hsM hsσ'
    cases sign with
    | plus =>
        exact htailPlus D hDtPlusD |>.2 s hsM hsσ'
    | minus =>
        exact htailMinus D hDtMinusD |>.2 s hsM hsσ'
  by_cases hMs : M ≤ s
  · exact hlarge sign s hMs hsσ
  · have hsM : s ≤ M := (lt_of_not_ge hMs).le
    have hheadD := hhead D hDhD sign s hs hsM
    have hpertD := hpert D hDpD sign s hs hsM
    have hlambdaDecay :
        lambda H sign D d 0 (M + 2) ≤
          (2 * C / M ^ 2) * lambda H sign D d 0 s :=
      lambda_fixed_endpoint_decay sign hM4 hD1 hs
        (h131C sign M s hM4 hs hsM) hpertD hH.toSection13HatContract.positive
    have htailD := hlarge sign (M + 2) (by linarith) hM2σ
    have hsplitD :
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) =
          (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
          (∫ t in M + 2..sourceSigma D d, qD H sign.opposite D d Δ t) :=
      qD_split_at_fixed_source_point (Δ := Δ) hH.toSection13HatContract
        sign hD1 hs hsM hM2σ
    let K : ℝ := (1 - 1 / sourceSigma D d) ^ (1 - Δ)
    let L : ℝ := lambda H sign D d 0 s
    have hKpos : 0 < K := by
      dsimp [K]
      apply Real.rpow_pos_of_pos
      have hσ1 : 1 < sourceSigma D d := by linarith [hM4, hM2σ]
      have hσ0 : 0 < sourceSigma D d := zero_lt_one.trans hσ1
      exact sub_pos.mpr ((div_lt_one hσ0).mpr hσ1)
    have hL : 0 < L := by
      dsimp [L]
      exact lambda_pos_of_source_range hH.toSection13HatContract sign hD1 hs
    have htailBound :
        (∫ t in M + 2..sourceSigma D d,
            qD H sign.opposite D d Δ t) <
          K * ((2 * C / M ^ 2) * L) := by
      exact htailD.trans_le (mul_le_mul_of_nonneg_left hlambdaDecay hKpos.le)
    rw [hsplitD]
    have hsum :
        K * (1 - gap / (4 * M)) * L +
            K * ((2 * C / M ^ 2) * L) < K * L := by
      have hcoefsum : 1 - gap / (4 * M) + 2 * C / M ^ 2 < 1 := by
        linarith
      calc
        K * (1 - gap / (4 * M)) * L + K * ((2 * C / M ^ 2) * L) =
            (K * L) * (1 - gap / (4 * M) + 2 * C / M ^ 2) := by ring
        _ < (K * L) * 1 := by
          exact mul_lt_mul_of_pos_left hcoefsum (mul_pos hKpos hL)
        _ = K * L := by ring
    change (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
        (∫ t in M + 2..sourceSigma D d, qD H sign.opposite D d Δ t) < K * L
    exact (add_lt_add_of_le_of_lt (by simpa [K, L, gap, mul_assoc] using hheadD)
      htailBound).trans hsum
