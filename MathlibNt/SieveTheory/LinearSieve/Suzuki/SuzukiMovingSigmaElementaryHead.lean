import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaClaim146SourceAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaCompactHead
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFixedGapRpowMargin

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The source cutoff eventually exceeds every fixed real number. -/
theorem exists_sourceSigma_fixed_lower_threshold
    (d L : ℝ) (hd : 0 ≤ d) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → L ≤ sourceSigma D d := by
  let X : ℝ := max 1 L
  have hX1 : 1 ≤ X := le_max_left _ _
  have hLX : L ≤ X := le_max_right _ _
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  let D₀ : ℝ := Real.exp (Real.exp X)
  have hD₀ : 1 < D₀ := Real.one_lt_exp_iff.mpr (Real.exp_pos X)
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos (Real.exp X)).trans_le hD
  have hlogD : Real.exp X ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 hD
  have hlogD1 : 1 ≤ Real.log D :=
    (Real.one_le_exp hXpos.le).trans hlogD
  have hpow1 : 1 ≤ (Real.log D) ^ (1 / d) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlogD1
        (by positivity : 0 ≤ 1 / d)
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner : Real.exp X ≤ Real.log (27 * D) := by
    rw [hlog27D]
    have hlog27 : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
    linarith
  have hll : X ≤ Real.log (Real.log (27 * D)) := by
    rw [← Real.log_exp X]
    exact Real.log_le_log (Real.exp_pos X) hinner
  unfold sourceSigma
  have hll0 : 0 ≤ Real.log (Real.log (27 * D)) := hXpos.le.trans hll
  calc
    L ≤ X := hLX
    _ ≤ Real.log (Real.log (27 * D)) := hll
    _ ≤ (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow1 hll0

private lemma one_le_fixed_perturbation
    {cutoff exponent point : ℝ}
    (hlog : 0 ≤ Real.log cutoff) (hpoint : 0 ≤ point) :
    1 ≤ perturbation cutoff exponent 0 point := by
  unfold perturbation
  simp only [add_zero]
  apply Real.one_le_rpow
  · exact le_add_of_nonneg_right
      (div_nonneg (Real.rpow_nonneg hpoint _) hlog)
  · exact hpoint

/-- The elementary fixed-compact perturbation input used by the source assembly. -/
theorem fixedCompactPerturbationContract
    {d M : ℝ} (_hd : 0 ≤ d) (hM : 4 ≤ M) :
    FixedCompactPerturbationContract d M := by
  have htpos : 0 < M + 2 := by linarith
  have hev : ∀ᶠ D : ℝ in atTop, perturbation D d 0 (M + 2) < 2 :=
    (tendsto_order.1 (tendsto_fixed_perturbation d (M + 2))).2 2 (by norm_num)
  obtain ⟨D₁, hD₁⟩ := (eventually_atTop.1 hev)
  let D₀ : ℝ := max 2 D₁
  refine ⟨D₀, by dsimp [D₀]; linarith [le_max_left (2 : ℝ) D₁], ?_⟩
  intro D hD sign s hs hsM
  have hD₁D : D₁ ≤ D := (le_max_right (2 : ℝ) D₁).trans hD
  have hD1 : 1 < D := by dsimp [D₀] at hD; linarith [le_max_left (2 : ℝ) D₁]
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hspos : 0 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs <;> linarith
  have hs1 : 1 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs <;> linarith
  have hPs : 1 ≤ perturbation D d 0 s :=
    one_le_fixed_perturbation hlog.le hspos.le
  calc
    perturbation D d 0 (M + 2) ≤ 2 := (hD₁ D hD₁D).le
    _ ≤ 2 * perturbation D d 0 s := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hPs (by norm_num : (0 : ℝ) ≤ 2)

private lemma fixed_gap_rpow_margin
    {gap M : ℝ} (hgap0 : 0 < gap) (hgap1 : gap < 1) (hM : 4 ≤ M) :
    (1 - 1 / (M + 2)) ^ (gap / 2) < 1 - gap / (4 * M) := by
  exact fixedGap_rpow_margin hgap0 hgap1 hM

/-- Corrected fixed-head source contract, with `gap = 1 - Δ`.  All thresholds
are chosen after the fixed cutoff `M`; no fixed-endpoint theorem is diagonalized. -/
theorem lemma133WeightedHeadContract_corrected
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {d Δ M : ℝ} (hd : 0 ≤ d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hM : 4 ≤ M) :
    Lemma133WeightedHeadContract H d Δ (1 - Δ) M := by
  let gap : ℝ := 1 - Δ
  let θ : ℝ := gap / 2
  let a : ℝ := (1 - 1 / (M + 2)) ^ θ
  let R : ℝ := 1 - gap / (4 * M)
  have hgap0 : 0 < gap := by dsimp [gap]; linarith
  have hgap1 : gap < 1 := by dsimp [gap]; linarith
  have ha0 : 0 < a := by
    dsimp [a, θ]
    apply Real.rpow_pos_of_pos
    have hMp2 : 0 < M + 2 := by linarith
    exact sub_pos.mpr ((div_lt_one hMp2).mpr (by linarith))
  have haR : a < R := by
    simpa [a, θ, R, gap] using fixed_gap_rpow_margin hgap0 hgap1 hM
  have hR0 : 0 < R := ha0.trans haR
  let q : ℝ := (R + a) / (2 * a)
  let k : ℝ := (R + a) / (2 * R)
  have hq1 : 1 < q := by dsimp [q]; rw [lt_div_iff₀ (mul_pos (by norm_num) ha0)]; nlinarith
  have hk1 : k < 1 := by dsimp [k]; rw [div_lt_one (mul_pos (by norm_num) hR0)]; nlinarith
  have hqa : q * a = (R + a) / 2 := by dsimp [q]; field_simp [ne_of_gt ha0]
  have hkR : k * R = (R + a) / 2 := by dsimp [k]; field_simp [ne_of_gt hR0]
  have hpertEv : ∀ᶠ D : ℝ in atTop, perturbation D d 0 (M + 2) < q :=
    (tendsto_order.1 (tendsto_fixed_perturbation d (M + 2))).2 q hq1
  obtain ⟨Dp, hDpEv⟩ := eventually_atTop.1 hpertEv
  have hweightEv : ∀ᶠ σ : ℝ in atTop, k < (1 - 1 / σ) ^ gap :=
    (tendsto_order.1 (tendsto_source_weight gap)).1 k hk1
  obtain ⟨S, hSEv⟩ := eventually_atTop.1 hweightEv
  obtain ⟨Ds, hDs1, hsource⟩ :=
    exists_sourceSigma_fixed_lower_threshold d S hd
  let D₀ : ℝ := max (max 2 Dp) Ds
  have hD₀1 : 1 < D₀ := by
    dsimp [D₀]
    have htwo : (2 : ℝ) ≤ max 2 Dp := le_max_left _ _
    have hinner : max 2 Dp ≤ max (max 2 Dp) Ds := le_max_left _ _
    linarith
  refine ⟨D₀, hD₀1, ?_⟩
  intro D hD sign s hs hsM
  have hDpD : Dp ≤ D :=
    (le_max_right (2 : ℝ) Dp).trans ((le_max_left (max 2 Dp) Ds).trans hD)
  have hDsD : Ds ≤ D := (le_max_right (max 2 Dp) Ds).trans hD
  have hD1 : 1 < D := by
    have : (2 : ℝ) ≤ D := (le_max_left (2 : ℝ) Dp).trans
      ((le_max_left (max 2 Dp) Ds).trans hD)
    linarith
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hσS : S ≤ sourceSigma D d := hsource D hDsD
  have hK : k < (1 - 1 / sourceSigma D d) ^ gap := hSEv _ hσS
  have hP : perturbation D d 0 (M + 2) < q := hDpEv D hDpD
  have hfactor : perturbation D d 0 (M + 2) * a <
      (1 - 1 / sourceSigma D d) ^ gap * R := by
    calc
      perturbation D d 0 (M + 2) * a < q * a :=
        mul_lt_mul_of_pos_right hP ha0
      _ = k * R := hqa.trans hkR.symm
      _ < (1 - 1 / sourceSigma D d) ^ gap * R :=
        mul_lt_mul_of_pos_right hK hR0
  have hspos : 0 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs <;> linarith
  have hs1 : 1 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs <;> linarith
  have hPs : 1 ≤ perturbation D d 0 s :=
    one_le_fixed_perturbation hlog.le hspos.le
  have htail := lemma13_3_weightedTail_strict_closedRange hH sign
    (show 0 ≤ θ by dsimp [θ]; positivity) hs (show s ≤ M + 2 by linarith)
  have hqcont := continuousOn_qD_Icc_of_contract (d := d) hH sign.opposite hD1
    hs1 (σ := M + 2) (Δ := Δ)
  have htailcont : ContinuousOn (hatTailIntegrand H sign) (Icc s (M + 2)) := by
    apply continuousOn_id.mul
    exact (hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const) (by
        intro t ht
        exact sub_pos.mpr (hs1.trans_le ht.1))
  have hratio : ContinuousOn (fun t : ℝ => (t - 1) / t) (Icc s (M + 2)) :=
    (continuousOn_id.sub continuousOn_const).div continuousOn_id (by
      intro t ht
      exact ne_of_gt (hspos.trans_le ht.1))
  have hwcont : ContinuousOn
      (fun t : ℝ => ((t - 1) / t) ^ θ * hatTailIntegrand H sign t)
      (Icc s (M + 2)) := by
    apply (hratio.rpow continuousOn_const _).mul htailcont
    intro t ht
    left
    exact ne_of_gt (div_pos (sub_pos.mpr (hs1.trans_le ht.1)) (hspos.trans_le ht.1))
  let K : ℝ := (1 - 1 / sourceSigma D d) ^ gap
  let C : ℝ := K * R * perturbation D d 0 s
  have hk0 : 0 < k := by
    dsimp [k]
    positivity
  have hKpos : 0 < K := by simpa [K] using hk0.trans hK
  have hK0 : 0 ≤ K := hKpos.le
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hKpos hR0)
      (lt_of_lt_of_le zero_lt_one hPs)
  have hpoint : ∀ t ∈ Icc s (M + 2),
      qD H sign.opposite D d Δ t ≤
        C * (((t - 1) / t) ^ θ * hatTailIntegrand H sign t) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have htm0 : 0 < t - 1 := sub_pos.mpr ht1
    have htM : t ≤ M + 2 := ht.2
    have htd : t ^ d ≤ (M + 2) ^ d :=
      Real.rpow_le_rpow ht0.le htM hd
    have hbase : 1 + t ^ d / Real.log D ≤ 1 + (M + 2) ^ d / Real.log D := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right htd hlog.le)
    have hbase0 : 1 ≤ 1 + t ^ d / Real.log D := by
      have : 0 ≤ t ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg ht0.le _) hlog.le
      linarith
    have hbaseM0 : 0 ≤ 1 + (M + 2) ^ d / Real.log D := by
      have : 0 ≤ (M + 2) ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ M + 2) _) hlog.le
      linarith
    have houter : (1 + t ^ d / Real.log D) ^ (t - 1) ≤
        perturbation D d 0 (M + 2) := by
      calc
        (1 + t ^ d / Real.log D) ^ (t - 1) ≤
            (1 + (M + 2) ^ d / Real.log D) ^ (t - 1) :=
          Real.rpow_le_rpow (zero_le_one.trans hbase0) hbase (by linarith)
        _ ≤ (1 + (M + 2) ^ d / Real.log D) ^ (M + 2) :=
          Real.rpow_le_rpow_of_exponent_le (hbase0.trans hbase) (by linarith)
        _ = perturbation D d 0 (M + 2) := by simp [perturbation]
    let b : ℝ := (t - 1) / t
    have hb0 : 0 < b := div_pos htm0 ht0
    have hbM : b ≤ 1 - 1 / (M + 2) := by
      dsimp [b]
      calc
        (t - 1) / t = 1 - 1 / t := by field_simp [ne_of_gt ht0]
        _ ≤ 1 - 1 / (M + 2) := by
          gcongr
    have hbpow : b ^ θ ≤ a := by
      dsimp [a]
      exact Real.rpow_le_rpow hb0.le hbM (by dsimp [θ]; positivity)
    have hsmall : (1 + t ^ d / Real.log D) ^ (t - 1) * b ^ θ ≤
        perturbation D d 0 (M + 2) * a :=
      mul_le_mul houter hbpow (Real.rpow_nonneg hb0.le _) (by
        rw [perturbation]
        simpa only [add_zero] using Real.rpow_nonneg hbaseM0 (M + 2))
    have hbudget : perturbation D d 0 (M + 2) * a < C := by
      dsimp [C]
      calc
        perturbation D d 0 (M + 2) * a < K * R := by simpa [K] using hfactor
        _ = K * R * 1 := by ring
        _ ≤ K * R * perturbation D d 0 s :=
          mul_le_mul_of_nonneg_left hPs (mul_nonneg hK0 hR0.le)
    have htail0 : 0 ≤ hatTailIntegrand H sign t :=
      (mul_pos ht0 (hH.positive sign.opposite (t - 1) htm0)).le
    have hfac :
        (1 + t ^ d / Real.log D) ^ (t - 1) * b ^ gap ≤ C * b ^ θ := by
      have hsplit : b ^ gap = b ^ θ * b ^ θ := by
        rw [← Real.rpow_add hb0]
        congr 1
        dsimp [θ]
        ring
      rw [hsplit]
      calc
        (1 + t ^ d / Real.log D) ^ (t - 1) * (b ^ θ * b ^ θ) =
            ((1 + t ^ d / Real.log D) ^ (t - 1) * b ^ θ) * b ^ θ := by ring
        _ ≤ (perturbation D d 0 (M + 2) * a) * b ^ θ :=
          mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hb0.le _)
        _ ≤ C * b ^ θ :=
          mul_le_mul_of_nonneg_right hbudget.le (Real.rpow_nonneg hb0.le _)
    calc
      qD H sign.opposite D d Δ t =
          ((1 + t ^ d / Real.log D) ^ (t - 1) * b ^ gap) *
            hatTailIntegrand H sign t := by
        simp only [qD, Section13HatLayers.kappaHat]
        norm_num [Real.rpow_one]
        dsimp [b, gap, hatTailIntegrand]
        rw [show t / (t - 1) = ((t - 1) / t)⁻¹ by rw [inv_div],
          Real.inv_rpow (div_pos htm0 ht0).le, ← Real.rpow_neg (div_pos htm0 ht0).le]
        rw [show 1 - Δ = 1 + (-Δ) by ring,
          Real.rpow_add (div_pos htm0 ht0), Real.rpow_one]
        field_simp [ne_of_gt ht0, ne_of_gt htm0]

      _ ≤ (C * b ^ θ) * hatTailIntegrand H sign t :=
        mul_le_mul_of_nonneg_right hfac htail0
      _ = C * (b ^ θ * hatTailIntegrand H sign t) := by ring
  have hmono : (∫ t in s..M + 2, qD H sign.opposite D d Δ t) ≤
      ∫ t in s..M + 2, C * (((t - 1) / t) ^ θ * hatTailIntegrand H sign t) :=
    intervalIntegral.integral_mono_on (by linarith)
      (hqcont.intervalIntegrable_of_Icc (by linarith))
      ((continuousOn_const.mul hwcont).intervalIntegrable_of_Icc (by linarith)) hpoint
  apply le_of_lt
  calc
    (∫ t in s..M + 2, qD H sign.opposite D d Δ t) ≤
        ∫ t in s..M + 2, C * (((t - 1) / t) ^ θ * hatTailIntegrand H sign t) := hmono
    _ = C * (∫ t in s..M + 2,
        ((t - 1) / t) ^ θ * hatTailIntegrand H sign t) :=
      by rw [intervalIntegral.integral_const_mul]
    _ < C * weightedHat H sign s := mul_lt_mul_of_pos_left htail hCpos
    _ = (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
        (1 - (1 - Δ) / (4 * M)) * lambda H sign D d 0 s := by
      rw [lambda_eq_perturb_mul_weightedHat]
      dsimp [C, K, R, gap]
      simp only [perturbation, add_zero]
      ring


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
