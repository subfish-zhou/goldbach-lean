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
  let B : ℝ := 2 * (d + 1) * K ^ 2 * A
  let M : ℝ := max 2 (Real.exp B)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hM1 : 1 < M := by
    dsimp [M]
    have : (1 : ℝ) < 2 := by norm_num
    exact this.trans_le (le_max_left _ _)
  obtain ⟨Ds, hDs, hsource⟩ :=
    exists_sourceSigma_fixed_lower_threshold d M hd.le
  let c₀ : ℝ := B * (1 + (d + 1) * Real.log 2)
  let c₁ : ℝ := B * d
  let Y : ℝ := max 1 (max (2 * d * c₀) ((4 * d * c₁) ^ 2))
  let X : ℝ := max 2 (max (Real.log 27) (Real.exp Y))
  let Dg : ℝ := Real.exp X
  let D₀ : ℝ := max Ds Dg
  have hDg : 1 < Dg := by
    dsimp [Dg, X]
    apply Real.one_lt_exp_iff.mpr
    have : (0 : ℝ) < 2 := by norm_num
    exact this.trans_le (le_max_left _ _)
  have hD₀ : 1 < D₀ := hDs.trans_le (le_max_left _ _)
  refine ⟨M, hd, hM1, D₀, hD₀, ?_⟩
  intro D hD
  have hDsD : Ds ≤ D := (le_max_left Ds Dg).trans hD
  have hDgD : Dg ≤ D := (le_max_right Ds Dg).trans hD
  have hMσ : M ≤ sourceSigma D d := hsource D hDsD
  refine ⟨hMσ, ?_⟩
  intro t hMt htσ
  let x : ℝ := Real.log D
  let y : ℝ := Real.log x
  let L : ℝ := Real.log (Real.log (27 * D))
  have hD1 : 1 < D := hD₀.trans_le hD
  have hx0 : 0 < x := by
    dsimp [x]
    exact Real.log_pos hD1
  have hXle : X ≤ x := by
    have hDpos : 0 < D := zero_lt_one.trans hD1
    have : Real.exp X ≤ D := by simpa [Dg] using hDgD
    exact (Real.le_log_iff_exp_le hDpos).2 this
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hXle
  have hlog27x : Real.log 27 ≤ x :=
    (le_max_left (Real.log 27) (Real.exp Y)).trans ((le_max_right 2 _).trans hXle)
  have hxy : Y ≤ y := by
    have hEy : Real.exp Y ≤ x :=
      (le_max_right (Real.log 27) (Real.exp Y)).trans ((le_max_right 2 _).trans hXle)
    dsimp [y]
    rw [← Real.log_exp Y]
    exact Real.log_le_log (Real.exp_pos Y) hEy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hxy
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hL0 : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt (zero_lt_one.trans hD1))]
    have hlog27 : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have ht0 : 0 < t := zero_lt_one.trans hM1 |> fun h => h.trans_le hMt
  have hxp0 : 0 < x ^ (1 / d) := Real.rpow_pos_of_pos hx0 _
  have htσ' : t ≤ x ^ (1 / d) * L := by
    simpa [x, L, sourceSigma] using htσ
  by_cases hcut : t ≤ x ^ (1 / d)
  · have hz1 : t ^ d / x ≤ 1 := by
      simpa [x] using
        source_cutoff_case_one_bound (D := D) (Real.log_pos hD1) hd ht0 hcut
    have hlogu : Real.log (1 + t ^ d / x) ≤ 1 := by
      have hpos : 0 < 1 + t ^ d / x := by
        have : 0 ≤ t ^ d / x := div_nonneg (Real.rpow_nonneg ht0.le _) hx0.le
        linarith
      have hle : Real.log (1 + t ^ d / x) ≤ t ^ d / x := by
        linarith [Real.log_le_sub_one_of_pos hpos]
      exact hle.trans hz1
    have hmax : max 1 (Real.log (1 + t ^ d / x)) ≤ 1 := by
      exact (max_le_iff.2 ⟨le_rfl, hlogu⟩)
    have hBt : B ≤ Real.log (Real.exp 1 * t) := by
      have hExp : Real.exp B ≤ t := (le_max_right 2 (Real.exp B)).trans hMt
      have hlogt : B ≤ Real.log t := by
        rw [← Real.log_exp B]
        exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos B) ht0 hExp
      rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt ht0), Real.log_exp]
      linarith
    calc
      2 * (d + 1) * K ^ 2 * A * max 1 (Real.log (1 + t ^ d / Real.log D))
          = B * max 1 (Real.log (1 + t ^ d / x)) := by
              dsimp [B, x]
      _ ≤ B * 1 := by
        gcongr
      _ = B := by ring
      _ ≤ Real.log (Real.exp 1 * t) := hBt
  · have hcut' : x ^ (1 / d) < t := lt_of_not_ge hcut
    have hz1 : 1 ≤ t ^ d / x := by
      rw [one_le_div hx0]
      have hp := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hcut'.le hd.le
      have hxpow : (x ^ (1 / d)) ^ d = x := by
        rw [← Real.rpow_mul hx0.le]
        have : (1 / d) * d = 1 := by field_simp
        rw [this, Real.rpow_one]
      rwa [hxpow] at hp
    have hbasePos : 0 < 1 + t ^ d / x := by
      have : 0 ≤ t ^ d / x := div_nonneg (Real.rpow_nonneg ht0.le _) hx0.le
      linarith
    have huz : 0 < t ^ d / x := lt_of_lt_of_le zero_lt_one hz1
    have hlogUpper : Real.log (1 + t ^ d / x) ≤
        Real.log 2 + Real.log (t ^ d / x) := by
      have h2z : 1 + t ^ d / x ≤ 2 * (t ^ d / x) := by linarith
      have h2zpos : 0 < 2 * (t ^ d / x) := by positivity
      have hmono := Real.strictMonoOn_log.monotoneOn hbasePos h2zpos h2z
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt huz)] at hmono
      exact hmono
    have hLpow : t ^ d / x ≤ L ^ d := by
      rw [div_le_iff₀ hx0]
      have htd : t ^ d ≤ (x ^ (1 / d) * L) ^ d :=
        Real.rpow_le_rpow ht0.le htσ' hd.le
      calc
        t ^ d ≤ (x ^ (1 / d) * L) ^ d := htd
        _ = x * L ^ d := by
          rw [Real.mul_rpow (Real.rpow_nonneg hx0.le _) hL0.le]
          rw [← Real.rpow_mul hx0.le]
          have : (1 / d) * d = 1 := by field_simp
          rw [this, Real.rpow_one]
        _ = L ^ d * x := by ring
    have hlogRatio : Real.log (t ^ d / x) ≤ d * Real.log L := by
      have hmono := Real.strictMonoOn_log.monotoneOn huz
        (Real.rpow_pos_of_pos hL0 d) hLpow
      rwa [Real.log_rpow hL0] at hmono
    have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
      dsimp [x]
      rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt (zero_lt_one.trans hD1))]
    have hinnerLe : Real.log (27 * D) ≤ 2 * x := by
      rw [hlog27D]
      linarith
    have hLle : L ≤ Real.log (2 * x) := by
      dsimp [L]
      have hleft : 0 < Real.log (27 * D) := by
        rw [hlog27D]
        have hlog27 : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
        linarith
      have hright : 0 < 2 * x := by positivity
      exact Real.strictMonoOn_log.monotoneOn hleft hright hinnerLe
    have hlog2le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
    have hlog2x : Real.log (2 * x) = Real.log 2 + y := by
      dsimp [y]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx0)]
    have hLle2y : L ≤ 2 * y := by
      rw [hlog2x] at hLle
      linarith
    have hlogL : Real.log L ≤ Real.log 2 + Real.log y := by
      have h2ypos : 0 < 2 * y := by positivity
      have hmono := Real.strictMonoOn_log.monotoneOn hL0 h2ypos hLle2y
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hy0)] at hmono
      exact hmono
    have hylog : Real.log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
      have h := Real.log_le_rpow_div hy0.le (by positivity : 0 < (1 / 2 : ℝ))
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    have hc₀bound : c₀ ≤ y / (2 * d) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * d)).2
      have hYc₀ : 2 * d * c₀ ≤ y := by
        exact (le_max_left (2 * d * c₀) ((4 * d * c₁) ^ 2)).trans
          ((le_max_right 1 (max (2 * d * c₀) ((4 * d * c₁) ^ 2))).trans hxy)
      linarith
    have hc₁sqrt : 2 * c₁ * y ^ (1 / 2 : ℝ) ≤ y / (2 * d) := by
      have hYc₁ : (4 * d * c₁) ^ 2 ≤ y := by
        exact (le_max_right (2 * d * c₀) ((4 * d * c₁) ^ 2)).trans
          ((le_max_right 1 (max (2 * d * c₀) ((4 * d * c₁) ^ 2))).trans hxy)
      have hroot : 4 * d * c₁ ≤ y ^ (1 / 2 : ℝ) := by
        apply le_of_sq_le_sq _ (Real.rpow_nonneg hy0.le _)
        calc
          (4 * d * c₁) ^ 2 ≤ y := hYc₁
          _ = (y ^ (1 / 2 : ℝ)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
            norm_num
      have hmul : (4 * d * c₁) * y ^ (1 / 2 : ℝ) ≤ y := by
        have hyroot0 : 0 ≤ y ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy0.le _
        calc
          (4 * d * c₁) * y ^ (1 / 2 : ℝ) ≤
              y ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) := by
                exact mul_le_mul_of_nonneg_right hroot hyroot0
          _ = y := by
            rw [← Real.rpow_add hy0]
            norm_num
      apply (le_div_iff₀ (by positivity : 0 < 2 * d)).2
      have : (2 * c₁ * y ^ (1 / 2 : ℝ)) * (2 * d) ≤ y := by
        calc
          (2 * c₁ * y ^ (1 / 2 : ℝ)) * (2 * d) =
              (4 * d * c₁) * y ^ (1 / 2 : ℝ) := by ring
          _ ≤ y := hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hc₁bound : c₁ * Real.log y ≤ y / (2 * d) := by
      calc
        c₁ * Real.log y ≤ c₁ * (2 * y ^ (1 / 2 : ℝ)) := by
          gcongr
        _ = 2 * c₁ * y ^ (1 / 2 : ℝ) := by ring
        _ ≤ y / (2 * d) := hc₁sqrt
    have hmainY : B * (1 + Real.log 2 + d * Real.log L) ≤ y / d := by
      have hstep :
          B * (1 + Real.log 2 + d * Real.log L) ≤ c₀ + c₁ * Real.log y := by
        calc
          B * (1 + Real.log 2 + d * Real.log L) ≤
              B * (1 + Real.log 2 + d * (Real.log 2 + Real.log y)) := by
                gcongr
          _ = c₀ + c₁ * Real.log y := by
                dsimp [c₀, c₁]
                ring
      calc
        B * (1 + Real.log 2 + d * Real.log L) ≤ c₀ + c₁ * Real.log y := hstep
        _ ≤ y / (2 * d) + y / (2 * d) := add_le_add hc₀bound hc₁bound
        _ = y / d := by
          ring_nf
    have hlogtLower : y / d ≤ Real.log t := by
      have hmono := Real.strictMonoOn_log.monotoneOn hxp0 ht0 hcut'.le
      rw [Real.log_rpow hx0] at hmono
      simpa [y, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmono
    have hmax :
        max 1 (Real.log (1 + t ^ d / x)) ≤ 1 + Real.log 2 + d * Real.log L := by
      calc
        max 1 (Real.log (1 + t ^ d / x)) ≤ 1 + Real.log (1 + t ^ d / x) :=
          max_one_le_one_add _ (by
            have : 1 ≤ 1 + t ^ d / x := by
              have hz0 : 0 ≤ t ^ d / x :=
                div_nonneg (Real.rpow_nonneg ht0.le _) hx0.le
              linarith
            exact Real.log_nonneg this)
        _ ≤ 1 + (Real.log 2 + Real.log (t ^ d / x)) :=
          add_le_add le_rfl hlogUpper
        _ ≤ 1 + (Real.log 2 + d * Real.log L) :=
          add_le_add le_rfl (add_le_add le_rfl hlogRatio)
        _ = 1 + Real.log 2 + d * Real.log L := by ring
    calc
      2 * (d + 1) * K ^ 2 * A * max 1 (Real.log (1 + t ^ d / Real.log D))
          = B * max 1 (Real.log (1 + t ^ d / x)) := by
              dsimp [B, x]
      _ ≤ B * (1 + Real.log 2 + d * Real.log L) := by
        gcongr
      _ ≤ y / d := hmainY
      _ ≤ Real.log t := hlogtLower
      _ ≤ Real.log (Real.exp 1 * t) := by
        rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt ht0), Real.log_exp]
        linarith

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
    (hH : Section13HatContract H β) (sign : ErrorSign)
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
  convert mul_le_mul_of_nonneg_left hmain hp0 using 1 <;> ring

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
