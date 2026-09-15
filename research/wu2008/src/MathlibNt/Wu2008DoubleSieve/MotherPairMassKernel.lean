import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairData

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology Interval

noncomputable def clipH (U t u : ℝ) : ℝ := 1 / (1 - min U t - min U u)
noncomputable def kernelSection (U C D t : ℝ) : ℝ :=
  ∫ u in gamma5MassSectionStart C D t..D, clipH U t u / u

theorem clipH_bounds {U : ℝ} (hU : U < 1/2) (t u : ℝ) :
    0 < clipH U t u ∧ clipH U t u ≤ 1/(1-2*U) := by
  have ht := min_le_left U t
  have hu := min_le_left U u
  have hg : 0 < 1-2*U := by linarith
  have hd : 1-2*U ≤ 1-min U t-min U u := by linarith
  exact ⟨one_div_pos.mpr (hg.trans_le hd), one_div_le_one_div_of_le hg hd⟩

theorem clipH_lipschitz {U : ℝ} (hU : U < 1/2) (x y u : ℝ) :
    |clipH U x u - clipH U y u| ≤ (1/(1-2*U)^2) * |x-y| := by
  have hg : 0 < 1-2*U := by linarith
  have hx : 1-2*U ≤ 1-min U x-min U u := by linarith [min_le_left U x, min_le_left U u]
  have hy : 1-2*U ≤ 1-min U y-min U u := by linarith [min_le_left U y, min_le_left U u]
  have hdx := hg.trans_le hx
  have hdy := hg.trans_le hy
  have hd : (1-2*U)^2 ≤ (1-min U x-min U u)*(1-min U y-min U u) := by
    nlinarith [mul_le_mul hx hy hg.le hdx.le]
  have he : clipH U x u - clipH U y u = (min U x-min U y) /
      ((1-min U x-min U u)*(1-min U y-min U u)) := by
    unfold clipH
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hdx hdy)]
  calc
    _ ≤ |x-y| / ((1-min U x-min U u)*(1-min U y-min U u)) :=
      div_le_div_of_nonneg_right (gamma5Mass_min_lipschitz U x y) (mul_pos hdx hdy).le
    _ ≤ |x-y| / (1-2*U)^2 := div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hg) hd
    _ = _ := by ring

theorem clipH_comm (U t u : ℝ) : clipH U t u = clipH U u t := by
  unfold clipH
  congr 1
  ring

theorem clipH_second_lipschitz {U : ℝ} (hU : U < 1/2) (t x y : ℝ) :
    |clipH U t x - clipH U t y| ≤ (1/(1-2*U)^2) * |x-y| := by
  rw [clipH_comm U t x, clipH_comm U t y]
  exact clipH_lipschitz hU x y t

theorem clipH_continuous {U : ℝ} (hU : U < 1/2) (t : ℝ) :
    ContinuousOn (clipH U t) (Icc (1/10:ℝ) (1/2)) :=
  primeOrdered_continuous_of_lipschitz (fun x _ y _ => clipH_second_lipschitz hU t x y)

theorem clipH_eq {U t u : ℝ} (ht : t ≤ U) (hu : u ≤ U) :
    clipH U t u = 1/(1-t-u) := by
  simp only [clipH, min_eq_right ht, min_eq_right hu]

theorem kernelSection_regular {U C D : ℝ} (hU : U < 1/2)
    (hC : 1/10 ≤ C) (hCD : C ≤ D) (hD : D ≤ 1/2) :
    (∀ t : ℝ, |kernelSection U C D t| ≤ 4*(1/(1-2*U))) ∧
    (∀ x y : ℝ, |kernelSection U C D x-kernelSection U C D y| ≤
      (4*(1/(1-2*U)^2)+10*(1/(1-2*U)))*|x-y|) := by
  have hg : 0 < 1-2*U := by linarith
  have hDm : D ∈ Icc (1/10:ℝ) (1/2) := ⟨hC.trans hCD,hD⟩
  have hm (t : ℝ) : gamma5MassSectionStart C D t ∈ Icc (1/10:ℝ) (1/2) :=
    ⟨hC.trans (gamma5Mass_start_bounds hCD t).1,(gamma5Mass_start_bounds hCD t).2.trans hD⟩
  have hb (t u : ℝ) : |clipH U t u| ≤ 1/(1-2*U) := by
    rw [abs_of_pos (clipH_bounds hU t u).1]
    exact (clipH_bounds hU t u).2
  constructor
  · intro t
    exact primeOrdered_integral_norm_le_four (hm t) hDm (by positivity) (fun u _ => hb t u)
  · intro x y
    have h1 := primeOrdered_integral_sub_bound
      (clipH_continuous hU x) (clipH_continuous hU y) (hm x) hDm
      (show 0 ≤ (1/(1-2*U)^2)*|x-y| by positivity)
      (fun u _ => clipH_lipschitz hU x y u)
    have h2 := primeOrdered_integral_norm_le (hm x) (hm y) (fun u _ => hb y u)
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (primeOrdered_integrable (clipH_continuous hU y) (hm x) (hm y))
      (primeOrdered_integrable (clipH_continuous hU y) (hm y) hDm)
    have he : (∫ u in gamma5MassSectionStart C D x..D, clipH U y u/u) -
        (∫ u in gamma5MassSectionStart C D y..D, clipH U y u/u) =
        ∫ u in gamma5MassSectionStart C D x..gamma5MassSectionStart C D y,
          clipH U y u/u := by linarith only [ha]
    have ht := abs_sub_le (kernelSection U C D x)
      (∫ u in gamma5MassSectionStart C D x..D, clipH U y u/u) (kernelSection U C D y)
    dsimp only [kernelSection] at ht ⊢
    rw [he] at ht
    rw [abs_sub_comm (gamma5MassSectionStart C D y)] at h2
    have hl := mul_le_mul_of_nonneg_left (gamma5Mass_start_lipschitz C D x y)
      (show 0 ≤ 10*(1/(1-2*U)) by positivity)
    nlinarith

theorem rectIntegral_eq {U A B C D : ℝ}
    (hAB : A ≤ B) (hB : B ≤ U) (hCD : C ≤ D) (hD : D ≤ U) :
    rectIntegral A B C D = ∫ t in A..B, kernelSection U C D t/t := by
  unfold rectIntegral kernelSection
  change (∫ t in A..B, ∫ u in gamma5MassSectionStart C D t..D, 1/(t*u*(1-t-u))) = _
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc A B := by simpa only [uIcc_of_le hAB] using ht
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  have hs := gamma5Mass_start_bounds hCD t
  have hu' : u ∈ Icc (gamma5MassSectionStart C D t) D := by
    simpa only [uIcc_of_le hs.2] using hu
  dsimp only
  rw [clipH_eq (ht'.2.trans hB) (hu'.2.trans hD)]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem rectIntegral_bounds {U A B C D : ℝ} (hU : U < 1/2)
    (hA : 1/10 ≤ A) (hAB : A ≤ B) (hB : B ≤ U)
    (hC : 1/10 ≤ C) (hCD : C ≤ D) (hD : D ≤ U) :
    0 ≤ rectIntegral A B C D ∧ rectIntegral A B C D ≤ 16*(1/(1-2*U)) := by
  have hg : 0 < 1-2*U := by linarith
  rw [rectIntegral_eq hAB hB hCD hD]
  constructor
  · apply intervalIntegral.integral_nonneg hAB
    intro t ht
    apply div_nonneg _ (by linarith [ht.1])
    apply intervalIntegral.integral_nonneg (gamma5Mass_start_bounds hCD t).2
    intro u hu
    apply div_nonneg (clipH_bounds hU t u).1.le
    have hs := (gamma5Mass_start_bounds hCD t).1
    linarith [hu.1]
  · have hh := (le_abs_self _).trans
      (primeOrdered_integral_norm_le_four ⟨hA,(hAB.trans hB).trans hU.le⟩
        ⟨hA.trans hAB,hB.trans hU.le⟩ (by positivity : 0 ≤ 4*(1/(1-2*U)))
        (fun t _ => (kernelSection_regular hU hC hCD (hD.trans hU.le)).1 t))
    exact hh.trans_eq (by ring)

end Wu2008DoubleSieve.MotherPair
