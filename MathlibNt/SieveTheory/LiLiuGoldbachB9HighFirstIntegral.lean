import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstLogRegion
import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstNormalized

open MeasureTheory Set
open scoped BigOperators Interval

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open MathlibNt.SieveTheory.LiuWeight

noncomputable section

set_option maxHeartbeats 800000

/-- The high C10 double integral, without the sieve factor eight. -/
def goldbachB9HighMainIntegral : ℝ :=
  ∫ u in (1 / 10 : ℝ)..(1 / 3),
    ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))

theorem intervalIntegrable_goldbachB9HighMainInner
    {u : ℝ} (hu : u ∈ Icc (1 / 10 : ℝ) (1 / 3)) :
    IntervalIntegrable (fun v : ℝ => 1 / (u * v * (1 - u - v)))
      volume (1 / 3) ((1 - u) / 2) :=
  intervalIntegrable_goldbachB9MainInner ⟨by linarith [hu.1], hu.2⟩

theorem goldbachB9HighMainIntegral_eq_iteratedSetIntegral :
    goldbachB9HighMainIntegral =
      ∫ u in Ioc (1 / 10 : ℝ) (1 / 3),
        ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v) := by
  unfold goldbachB9HighMainIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  change (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
    ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v)
  rw [intervalIntegral.integral_of_le (by linarith [hu.2] : (1 / 3 : ℝ) ≤ (1 - u) / 2)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v _
  exact (goldbachB9LogIntegrand_eq u v).symm

theorem goldbachB9HighSourceIndicator_integral_section (u : ℝ) :
    (∫ v, goldbachB9HighLogSourceRegion.indicator liuLogIntegrand (u, v)) =
      (Ioc (1 / 10 : ℝ) (1 / 3)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v)) u := by
  by_cases hu : u ∈ Ioc (1 / 10 : ℝ) (1 / 3)
  · rw [indicator_of_mem hu, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with v
    have hmem : (u, v) ∈ goldbachB9HighLogSourceRegion ↔
        v ∈ Ioc (1 / 3) ((1 - u) / 2) := and_iff_right hu
    change goldbachB9HighLogSourceRegion.indicator liuLogIntegrand (u, v) =
      (Ioc (1 / 3) ((1 - u) / 2)).indicator (fun v => liuLogIntegrand (u, v)) v
    by_cases hv : v ∈ Ioc (1 / 3) ((1 - u) / 2)
    · rw [indicator_of_mem (hmem.mpr hv), indicator_of_mem hv]
    · rw [indicator_of_notMem (fun h => hv (hmem.mp h)), indicator_of_notMem hv]
  · rw [indicator_of_notMem hu]
    apply integral_eq_zero_of_ae
    filter_upwards with v
    exact indicator_of_notMem (fun h => hu h.1) _

theorem intervalIntegrable_goldbachB9HighMainOuter :
    IntervalIntegrable
      (fun u : ℝ => ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v)))
      volume (1 / 10) (1 / 3) := by
  have hF := integrable_goldbachB9HighSourceIndicator
  rw [Measure.volume_eq_prod ℝ ℝ] at hF
  have hi := hF.integral_prod_left
  have hIndicator : Integrable ((Ioc (1 / 10 : ℝ) (1 / 3)).indicator
      (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v))) := by
    apply hi.congr
    filter_upwards with u
    exact goldbachB9HighSourceIndicator_integral_section u
  have hOn := (integrable_indicator_iff measurableSet_Ioc).mp hIndicator
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)).mpr
  apply hOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [intervalIntegral.integral_of_le (by linarith [hu.2] : (1 / 3 : ℝ) ≤ (1 - u) / 2)]
  simp only [goldbachB9LogIntegrand_eq]

/-- Fubini uses the integrability of this high source indicator. -/
theorem goldbachB9HighMainIntegral_eq_setIntegral :
    goldbachB9HighMainIntegral =
      ∫ x in goldbachB9HighLogSourceRegion, liuLogIntegrand x := by
  rw [goldbachB9HighMainIntegral_eq_iteratedSetIntegral]
  let F := goldbachB9HighLogSourceRegion.indicator liuLogIntegrand
  have hF : Integrable F := integrable_goldbachB9HighSourceIndicator
  have hFubini : (∫ z, F z) = ∫ u, ∫ v, F (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact integral_prod F hF
  calc
    _ = ∫ u, (Ioc (1 / 10 : ℝ) (1 / 3)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v)) u := by
      rw [integral_indicator measurableSet_Ioc]
    _ = ∫ u, ∫ v, F (u, v) := by
      apply integral_congr_ae
      filter_upwards with u
      exact (goldbachB9HighSourceIndicator_integral_section u).symm
    _ = ∫ z, F z := hFubini.symm
    _ = _ := integral_indicator measurableSet_goldbachB9HighLogSourceRegion

theorem goldbachB9HighMainIntegral_nonneg : 0 ≤ goldbachB9HighMainIntegral := by
  rw [goldbachB9HighMainIntegral_eq_setIntegral]
  apply setIntegral_nonneg measurableSet_goldbachB9HighLogSourceRegion
  intro x hx
  exact (goldbachB9LogIntegrand_bounds
    (goldbachB9HighLogSourceRegion_subset_ambientBox hx)).1

private def b9HighUnitBox : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

private theorem volume_b9HighUnitBox :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem b9HighIndicator_nonneg {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) (x : ℝ × ℝ) : 0 ≤ s.indicator f x := by
  classical
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx]
    exact h x hx
  · rw [indicator_of_notMem hx]

private theorem b9HighUpperIntegrand_majorized {n : ℕ} (hn : 0 < n) (x : ℝ × ℝ) :
    goldbachB9HighLogGridUpperIntegrand n x ≤
      goldbachB9HighLogSourceRegion.indicator liuLogIntegrand x +
        b9HighUnitBox.indicator (fun _ => 1600 / (n : ℝ)) x +
        (goldbachB9HighLeftStrip n).indicator (fun _ => (480 : ℝ)) x +
        (goldbachB9HighBottomStrip n).indicator (fun _ => (480 : ℝ)) x +
        (goldbachB9HighObliqueStrip n).indicator (fun _ => (480 : ℝ)) x := by
  have hS := b9HighIndicator_nonneg (fun x hx =>
    (goldbachB9LogIntegrand_bounds (goldbachB9HighLogSourceRegion_subset_ambientBox hx)).1) x
  have hU := b9HighIndicator_nonneg
    (s := b9HighUnitBox) (f := fun _ => 1600 / (n : ℝ)) (by intros; positivity) x
  have hL := b9HighIndicator_nonneg
    (s := goldbachB9HighLeftStrip n) (f := fun _ => (480 : ℝ)) (by intros; norm_num) x
  have hB := b9HighIndicator_nonneg
    (s := goldbachB9HighBottomStrip n) (f := fun _ => (480 : ℝ)) (by intros; norm_num) x
  have hO := b9HighIndicator_nonneg
    (s := goldbachB9HighObliqueStrip n) (f := fun _ => (480 : ℝ)) (by intros; norm_num) x
  by_cases hg : x ∈ goldbachB9HighLogGridRegion n
  · by_cases hs : x ∈ goldbachB9HighLogSourceRegion
    · have hb := goldbachB9HighLogGridRegion_subset_ambientBox hn hg
      have hu : x ∈ b9HighUnitBox :=
        ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
          ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩
      rw [indicator_of_mem hs, indicator_of_mem hu]
      linarith [goldbachB9HighLogGridUpperIntegrand_le_integrand_add hn hg]
    · rw [indicator_of_notMem hs]
      have hb := goldbachB9HighLogGridUpperIntegrand_le hn hg
      rcases goldbachB9HighLogGridRegion_excess_subset hn ⟨hg, hs⟩ with (hl | hd) | ho
      · rw [indicator_of_mem hl]
        linarith
      · rw [indicator_of_mem hd]
        linarith
      · rw [indicator_of_mem ho]
        linarith
  · rw [goldbachB9HighLogGridUpperIntegrand_eq_zero hg]
    linarith

theorem goldbachB9HighLogGridErrorConstant_pos : (0 : ℝ) < 10000 := by norm_num

/-- All three strip areas are those of the high domain, for every positive mesh. -/
theorem goldbachB9HighLogGridUpperSum_sub_mainIntegral_le (n : ℕ) (hn : 0 < n) :
    goldbachB9HighLogGridUpperSum n - goldbachB9HighMainIntegral ≤ 10000 / (n : ℝ) := by
  let fSource := goldbachB9HighLogSourceRegion.indicator liuLogIntegrand
  let fUnit := b9HighUnitBox.indicator (fun _ => 1600 / (n : ℝ))
  let fLeft := (goldbachB9HighLeftStrip n).indicator (fun _ => (480 : ℝ))
  let fBottom := (goldbachB9HighBottomStrip n).indicator (fun _ => (480 : ℝ))
  let fOblique := (goldbachB9HighObliqueStrip n).indicator (fun _ => (480 : ℝ))
  have hSource : Integrable fSource := integrable_goldbachB9HighSourceIndicator
  have hUnit : Integrable fUnit := by
    apply integrable_indicator_of_integrableOn (measurableSet_Icc.prod measurableSet_Icc)
    apply integrableOn_const
    · rw [volume_b9HighUnitBox]
      norm_num
    · finiteness
  have hLeft : Integrable fLeft := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB9HighLeftStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB9HighLeftStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hBottom : Integrable fBottom := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB9HighBottomStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB9HighBottomStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hOblique : Integrable fOblique := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB9HighObliqueStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB9HighObliqueStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hmono : (∫ x, goldbachB9HighLogGridUpperIntegrand n x) ≤
      ∫ x, (((fSource x + fUnit x) + fLeft x) + fBottom x) + fOblique x :=
    integral_mono (integrable_goldbachB9HighLogGridUpperIntegrand n hn)
      ((((hSource.add hUnit).add hLeft).add hBottom).add hOblique)
      (b9HighUpperIntegrand_majorized hn)
  rw [← goldbachB9HighLogGridUpperSum_eq_integral n hn] at hmono
  have hOuter := integral_add (((hSource.add hUnit).add hLeft).add hBottom) hOblique
  have hMid := integral_add ((hSource.add hUnit).add hLeft) hBottom
  have hInner := integral_add (hSource.add hUnit) hLeft
  have hFirst := integral_add hSource hUnit
  simp only [Pi.add_apply] at hOuter hMid hInner hFirst
  rw [hOuter, hMid, hInner, hFirst] at hmono
  dsimp [fSource, fUnit, fLeft, fBottom, fOblique, b9HighUnitBox] at hmono
  rw [integral_indicator measurableSet_goldbachB9HighLogSourceRegion,
    ← goldbachB9HighMainIntegral_eq_setIntegral,
    integral_indicator_const (1600 / (n : ℝ)) (measurableSet_Icc.prod measurableSet_Icc),
    integral_indicator_const (480 : ℝ) (measurableSet_goldbachB9HighLeftStrip n),
    integral_indicator_const (480 : ℝ) (measurableSet_goldbachB9HighBottomStrip n),
    integral_indicator_const (480 : ℝ) (measurableSet_goldbachB9HighObliqueStrip n),
    Measure.real_def, volume_b9HighUnitBox,
    Measure.real_def, volume_goldbachB9HighLeftStrip,
    Measure.real_def, volume_goldbachB9HighBottomStrip,
    Measure.real_def, volume_goldbachB9HighObliqueStrip] at hmono
  have hbottom : ((1 / 3 : ℝ) - 1 / 10) * goldbachB9BetaGridStep n =
      (7 / 120 : ℝ) / n := by
    unfold goldbachB9BetaGridStep goldbachB9BetaGridWidth
    ring
  have hoblique : ((1 / 3 : ℝ) - 1 / 10) *
      (goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2 =
        (329 / 3600 : ℝ) / n := by
    unfold goldbachB9AlphaGridStep goldbachB9BetaGridStep
      goldbachB9AlphaGridWidth goldbachB9BetaGridWidth
    ring
  rw [hbottom, hoblique] at hmono
  simp only [ENNReal.toReal_one, smul_eq_mul] at hmono
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (17 / 240 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (7 / 120 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (329 / 3600 : ℝ) / n)] at hmono
  have herr : 1600 / (n : ℝ) + (17 / 240 : ℝ) / n * 480 +
      (7 / 120 : ℝ) / n * 480 + (329 / 3600 : ℝ) / n * 480 ≤ 10000 / (n : ℝ) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp [hnreal.ne']
    norm_num
  linarith

theorem exists_goldbachB9HighLogGridUpperSum_le_mainIntegral_add
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ goldbachB9HighLogGridUpperSum n ≤ goldbachB9HighMainIntegral + δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((10000 : ℝ) / δ)
  have hnp : (0 : ℝ) < n := (div_pos (by norm_num) hδ).trans hn
  have hnNat : 0 < n := by exact_mod_cast hnp
  have herr : (10000 : ℝ) / n ≤ δ := by
    apply (div_le_iff₀ hnp).mpr
    have h := (div_lt_iff₀ hδ).mp hn
    nlinarith
  refine ⟨n, hnNat, ?_⟩
  linarith [goldbachB9HighLogGridUpperSum_sub_mainIntegral_le n hnNat]

/-- Choose the mesh from delta before taking its fixed-mesh prime-size limit. -/
theorem goldbachK9High_le_mainIntegral_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachK9High N ≤ goldbachB9HighMainIntegral + δ := by
  obtain ⟨n, hn, hmesh⟩ :=
    exists_goldbachB9HighLogGridUpperSum_le_mainIntegral_add (δ / 2) (by positivity)
  obtain ⟨N₀, hN₀, hfixed⟩ :=
    goldbachK9High_le_gridUpperSum_eventually n hn (δ / 2) (by positivity)
  exact ⟨N₀, hN₀, fun N hN => by linarith [hfixed N hN]⟩

theorem goldbachK9High_le_doubleIntegral_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachK9High N ≤
        (∫ u in (1 / 10 : ℝ)..(1 / 3),
          ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) + δ :=
  goldbachK9High_le_mainIntegral_eventually δ hδ

/-- The actual high S5 consumer, with every analytic error paid into delta. -/
theorem goldbachS5HighFirstClosed_normalized_upper_integral
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        (8 * goldbachB9HighMainIntegral + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  have hI := goldbachB9HighMainIntegral_nonneg
  have hden : 0 < goldbachB9HighMainIntegral + 10 := by linarith
  let t : ℝ := min (δ / (goldbachB9HighMainIntegral + 10)) 1
  have ht : 0 < t := lt_min (div_pos hδ hden) zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htd : t * (goldbachB9HighMainIntegral + 10) ≤ δ :=
    (le_div_iff₀ hden).mp (min_le_left _ _)
  have hcoef : (8 + t) * (goldbachB9HighMainIntegral + t) + t ≤
      8 * goldbachB9HighMainIntegral + δ := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  obtain ⟨Ns, hNs, hs⟩ := goldbachS5HighFirstClosed_normalized_upper t ε ht hε hεu
  obtain ⟨Nk, _hNk, hk⟩ := goldbachK9High_le_mainIntegral_eventually t ht
  refine ⟨max Ns Nk, hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hS := hs N ((le_max_left _ _).trans hN) hEven
  have hK := hk N ((le_max_right _ _).trans hN)
  have hscale : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log (N : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hpoint := add_le_add (mul_le_mul_of_nonneg_left hK
    (show 0 ≤ 8 + t by positivity)) (le_rfl : t ≤ t)
  exact hS.trans (mul_le_mul_of_nonneg_right (hpoint.trans hcoef) hscale)

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig