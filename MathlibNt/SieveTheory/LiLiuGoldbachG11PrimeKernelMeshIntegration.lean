import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelMeshRegion

open Filter MeasureTheory Set
open scoped BigOperators Topology Interval

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11MeshDensity (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  LiuWeight.liuLogDensity x.1 * LiuWeight.liuLogDensity x.2

def goldbachG11MeshIntegrand (h : ℝ → ℝ) (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  (h x.1.1 / x.1.2) * goldbachG11MeshDensity x

theorem continuousOn_goldbachG11MeshDensity :
    ContinuousOn goldbachG11MeshDensity goldbachG11MeshAmbient := by
  unfold goldbachG11MeshDensity LiuWeight.liuLogDensity
  apply ContinuousOn.mul
  · refine continuousOn_const.div (by fun_prop) ?_
    intro x hx
    exact mul_ne_zero (by linarith [hx.1.1.1]) (by linarith [hx.1.2.1])
  · refine continuousOn_const.div (by fun_prop) ?_
    intro x hx
    exact mul_ne_zero (by linarith [hx.2.1.1]) (by linarith [hx.2.2.1])

theorem goldbachG11MeshDensity_nonneg {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG11MeshAmbient) : 0 ≤ goldbachG11MeshDensity x := by
  have hr : 0 ≤ x.1.1 := by linarith [hx.1.1.1]
  have hq : 0 ≤ x.1.2 := by linarith [hx.1.2.1]
  have hs : 0 ≤ x.2.1 := by linarith [hx.2.1.1]
  have ht : 0 ≤ x.2.2 := by linarith [hx.2.2.1]
  exact mul_nonneg (div_nonneg zero_le_one (mul_nonneg hr hq))
    (div_nonneg zero_le_one (mul_nonneg hs ht))

theorem integrableOn_goldbachG11MeshDensity {s : Set ((ℝ × ℝ) × (ℝ × ℝ))}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachG11MeshAmbient) :
    IntegrableOn goldbachG11MeshDensity s := by
  exact continuousOn_goldbachG11MeshDensity.integrableOn_of_subset_isCompact
    isCompact_goldbachG11MeshAmbient hs hsub
      (lt_of_le_of_lt (measure_mono hsub) isCompact_goldbachG11MeshAmbient.measure_lt_top).ne

theorem integrable_goldbachG11MeshSource (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) :
    Integrable (goldbachG11MeshSource.indicator (goldbachG11MeshIntegrand h)) := by
  have hc : ContinuousOn (goldbachG11MeshIntegrand h) goldbachG11MeshAmbient := by
    apply ContinuousOn.mul
    · refine (hh.comp (by fun_prop) (fun _ hx => hx.1.1)).div (by fun_prop) ?_
      intro x hx
      linarith [hx.1.2.1]
    · exact continuousOn_goldbachG11MeshDensity
  have hsub : goldbachG11MeshSource ⊆ goldbachG11MeshAmbient :=
    fun _ hx => goldbachG11MeshBox_subset_ambient hx.1
  exact (integrable_indicator_iff measurableSet_goldbachG11MeshSource).mpr
    (hc.integrableOn_of_subset_isCompact isCompact_goldbachG11MeshAmbient
      measurableSet_goldbachG11MeshSource hsub
        (lt_of_le_of_lt (measure_mono hsub) isCompact_goldbachG11MeshAmbient.measure_lt_top).ne)

theorem goldbachG11LogBoxMass_eq_meshIntegral (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    goldbachG11LogBoxMass (goldbachG11MeshLo n j) (goldbachG11MeshHi n j) =
      ∫ x in goldbachG11MeshCell n j, goldbachG11MeshDensity x := by
  unfold goldbachG11MeshCell goldbachG11MeshDensity
  rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), setIntegral_prod_mul]
  unfold goldbachG11LogBoxMass
  have hp (i : Fin 4) : 0 < goldbachG11MeshLo n j i := goldbachG11MeshPoint_pos _ _
  have hl (i : Fin 4) : goldbachG11MeshLo n j i < goldbachG11MeshHi n j i :=
    goldbachG11MeshPoint_strictMono n (Nat.lt_succ_self _)
  rw [LiuWeight.logarithmicRectangleMass_eq_setIntegral (hp 0) (hl 0) (hp 1) (hl 1),
    LiuWeight.logarithmicRectangleMass_eq_setIntegral (hp 2) (hl 2) (hp 3) (hl 3)]

private theorem g11_integral_four (F : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) (hF : Integrable F) :
    (∫ x, F x) = ∫ r : ℝ, ∫ q : ℝ, ∫ s : ℝ, ∫ t : ℝ, F ((r, q), (s, t)) := by
  simp only [Measure.volume_eq_prod] at hF ⊢
  rw [integral_prod F hF, integral_prod _ hF.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hF.prod_right_ae] with r hr
  apply integral_congr_ae
  filter_upwards [hr] with q hq
  exact integral_prod _ hq

theorem goldbachG11MeshSource_mem_iff (r q s t : ℝ) :
    ((r, q), (s, t)) ∈ goldbachG11MeshSource ↔
      r ∈ Ioc (4 / 53 : ℝ) (4 / 33) ∧ q ∈ Icc r (4 / 33) ∧
        s ∈ Icc q (4 / 33) ∧ t ∈ Icc s (4 / 33) := by
  constructor
  · intro hx
    exact ⟨hx.1.1.1, ⟨hx.2.1, hx.1.1.2.2⟩,
      ⟨hx.2.2.1, hx.1.2.1.2⟩, ⟨hx.2.2.2, hx.1.2.2.2⟩⟩
  · rintro ⟨hr, hq, hs, ht⟩
    exact ⟨⟨⟨hr, ⟨hr.1.trans_le hq.1, hq.2⟩⟩,
      ⟨⟨(hr.1.trans_le hq.1).trans_le hs.1, hs.2⟩,
        ⟨((hr.1.trans_le hq.1).trans_le hs.1).trans_le ht.1, ht.2⟩⟩⟩,
      hq.1, hs.1, ht.1⟩

private theorem g11_source_indicator (f : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) (r q s t : ℝ) :
    goldbachG11MeshSource.indicator f ((r, q), (s, t)) =
      (Ioc (4 / 53 : ℝ) (4 / 33)).indicator (fun r =>
        (Icc r (4 / 33)).indicator (fun q =>
          (Icc q (4 / 33)).indicator (fun s =>
            (Icc s (4 / 33)).indicator (fun t => f ((r, q), (s, t))) t) s) q) r := by
  classical
  simp only [Set.indicator_apply, goldbachG11MeshSource_mem_iff]
  split_ifs <;> simp_all

private theorem g11_integral_parameter_indicator (s : Set ℝ) (x : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ y, s.indicator (fun x => f x y) x) = s.indicator (fun x => ∫ y, f x y) x := by
  classical
  by_cases hx : x ∈ s <;> simp [hx]

theorem goldbachG11PrimeIntegral_eq_meshSource (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) :
    goldbachG11PrimeIntegral h =
      ∫ x, goldbachG11MeshSource.indicator (goldbachG11MeshIntegrand h) x := by
  rw [g11_integral_four _ (integrable_goldbachG11MeshSource h hh)]
  simp_rw [g11_source_indicator, g11_integral_parameter_indicator,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioc]
  unfold goldbachG11PrimeIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr.2]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro q hq
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hq.2]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs.2]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  simp only [goldbachG11MeshIntegrand, goldbachG11MeshDensity, LiuWeight.liuLogDensity,
    div_eq_mul_inv, mul_inv, pow_two]
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig