import MathlibNt.Analysis.IntegralExcessCover
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


/-- Fubini uses the integrability of this high source indicator. -/
theorem goldbachB9HighMainIntegral_eq_setIntegral :
    goldbachB9HighMainIntegral =
      ∫ x in goldbachB9HighLogSourceRegion, liuLogIntegrand x := by
  rw [goldbachB9HighMainIntegral_eq_iteratedSetIntegral]
  exact (MathlibNt.Analysis.setIntegral_moving_Ioc_eq_iterated
    (Ioc (1 / 10 : ℝ) (1 / 3)) (fun _ => (1 / 3 : ℝ)) (fun u => (1 - u) / 2)
    liuLogIntegrand measurableSet_Ioc measurableSet_goldbachB9HighLogSourceRegion
    (integrableOn_goldbachB9LogIntegrand measurableSet_goldbachB9HighLogSourceRegion
      goldbachB9HighLogSourceRegion_subset_ambientBox)).symm

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

/-- All three strip areas are those of the high domain, for every positive mesh. -/
theorem goldbachB9HighLogGridUpperSum_sub_mainIntegral_le (n : ℕ) (hn : 0 < n) :
    goldbachB9HighLogGridUpperSum n - goldbachB9HighMainIntegral ≤ 10000 / (n : ℝ) := by
  let E : Fin 3 → Set (ℝ × ℝ) :=
    ![goldbachB9HighLeftStrip n, goldbachB9HighBottomStrip n, goldbachB9HighObliqueStrip n]
  have hbound := MathlibNt.Analysis.IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover
    volume (goldbachB9HighLogGridRegion n) goldbachB9HighLogSourceRegion b9HighUnitBox E
    (goldbachB9HighLogGridUpperIntegrand n) liuLogIntegrand (1600 / (n : ℝ)) 480
    (integrable_goldbachB9HighLogGridUpperIntegrand n hn)
    (integrableOn_goldbachB9LogIntegrand measurableSet_goldbachB9HighLogSourceRegion
      goldbachB9HighLogSourceRegion_subset_ambientBox)
    measurableSet_goldbachB9HighLogSourceRegion (measurableSet_Icc.prod measurableSet_Icc)
    (by dsimp [b9HighUnitBox]; rw [volume_b9HighUnitBox]; norm_num)
    (by intro i; fin_cases i <;> simp [E, measurableSet_goldbachB9HighLeftStrip,
      measurableSet_goldbachB9HighBottomStrip, measurableSet_goldbachB9HighObliqueStrip])
    (by
      intro i
      fin_cases i <;> dsimp [E]
      · rw [volume_goldbachB9HighLeftStrip]; exact ENNReal.ofReal_ne_top
      · rw [volume_goldbachB9HighBottomStrip]; exact ENNReal.ofReal_ne_top
      · rw [volume_goldbachB9HighObliqueStrip]; exact ENNReal.ofReal_ne_top)
    (by positivity) (by norm_num)
    (fun _ hx => (goldbachB9LogIntegrand_bounds
      (goldbachB9HighLogSourceRegion_subset_ambientBox hx)).1)
    (fun _ hx => goldbachB9HighLogGridUpperIntegrand_eq_zero hx)
    (by
      intro x hx
      have hb := goldbachB9HighLogSourceRegion_subset_ambientBox hx.2
      exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
        ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩)
    (fun _ hx => goldbachB9HighLogGridUpperIntegrand_le_integrand_add hn hx.1)
    (by
      intro x hx
      rcases goldbachB9HighLogGridRegion_excess_subset hn hx with (hl | hd) | ho
      · exact ⟨0, hl⟩
      · exact ⟨1, hd⟩
      · exact ⟨2, ho⟩)
    (fun _ hx => goldbachB9HighLogGridUpperIntegrand_le hn hx.1)
  rw [← goldbachB9HighLogGridUpperSum_eq_integral n hn,
    ← goldbachB9HighMainIntegral_eq_setIntegral] at hbound
  simp only [E, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    Measure.real_def, b9HighUnitBox, volume_b9HighUnitBox, ENNReal.toReal_one, one_mul,
    volume_goldbachB9HighLeftStrip, volume_goldbachB9HighBottomStrip,
    volume_goldbachB9HighObliqueStrip] at hbound
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
  rw [hbottom, hoblique] at hbound
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (17 / 240 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (7 / 120 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (329 / 3600 : ℝ) / n)] at hbound
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