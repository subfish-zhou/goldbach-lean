import W03Weights

namespace WuTarget.W03
open Set MeasureTheory QuarterTrim DirectFiniteF6 NodeExtension
open scoped Classical
noncomputable section

def sumUpper (j : Fin 21) : ℝ := 1/2 - alpha * rNode j.val
def sumLower (j : Fin 21) : ℝ := 1/2 - alpha * rNode (j.val + 1)
def sliceLower (j : Fin 21) (x : ℝ) : ℝ := max beta (sumLower j - x)
def sliceUpper (j : Fin 21) (x : ℝ) : ℝ := min (1/4) (sumUpper j - x)
def sliceLength (j : Fin 21) (x : ℝ) : ℝ :=
  max 0 (sliceUpper j x - sliceLower j x)

theorem sum_bounds (j : Fin 21) :
    sumLower j ≤ sumUpper j ∧ sumUpper j ≤ 1/2-2*alpha := by
  have hr := rNode_mono (show j.val ≤ j.val + 1 by omega)
  have hn : (2 : ℝ) ≤ rNode j.val := by
    dsimp [rNode]
    exact le_add_of_nonneg_right (by positivity)
  have ha := alpha_pos
  dsimp [sumLower, sumUpper]
  constructor <;> nlinarith

theorem slice_domain (j : Fin 21) {x y : ℝ} (hx : x ∈ Icc alpha beta)
    (hy : y ∈ Icc (sliceLower j x) (sliceUpper j x)) :
    (x,y) ∈ StaircaseShrink.domain 0 := by
  apply (StaircaseShrink.domain_iff 0 x y).mpr
  have hl := (le_max_left beta (sumLower j-x)).trans hy.1
  have hu := hy.2.trans (min_le_left (1/4 : ℝ) (sumUpper j-x))
  have hs := hy.2.trans (min_le_right (1/4 : ℝ) (sumUpper j-x))
  exact ⟨hx.1, hx.2, hl, by linarith, by linarith [sum_bounds j]⟩

theorem slice_cell (j : Fin 21) {x y : ℝ}
    (hy : y ∈ Ioo (sliceLower j x) (sliceUpper j x)) : cell j (u x y) := by
  have hl := (le_max_right beta (sumLower j-x)).trans_lt hy.1
  have hu := hy.2.trans_le (min_le_right (1/4 : ℝ) (sumUpper j-x))
  constructor
  · apply (lt_div_iff₀ alpha_pos).mpr
    dsimp [sumUpper] at hu
    linarith
  · apply (div_le_iff₀ alpha_pos).mpr
    dsimp [sumLower] at hl
    linarith

def denominatorCap : ℝ := beta * (1/2-alpha)^2 / 4

theorem denominatorCap_pos : 0 < denominatorCap := by
  norm_num [denominatorCap, alpha, beta]

theorem denominator_upper {x y : ℝ} (h : (x,y) ∈ StaircaseShrink.domain 0) :
    x*y*(1/2-x-y) ≤ denominatorCap := by
  have hx0 := alpha_pos.le.trans h.1.1
  have hxhalf : x ≤ 1/2 := by
    have hb : beta ≤ (1/2 : ℝ) := by norm_num [beta]
    exact h.1.2.trans hb
  have hsq : (1/2-x)^2 ≤ (1/2-alpha)^2 := by
    nlinarith [h.1.1]
  have hyz : y*(1/2-x-y) ≤ (1/2-x)^2/4 := by
    nlinarith only [sq_nonneg (y-(1/2-x)/2)]
  have h1 := mul_le_mul_of_nonneg_left hyz hx0
  have h2 := mul_le_mul_of_nonneg_left hsq hx0
  have h3 := mul_le_mul_of_nonneg_right h.1.2 (sq_nonneg (1/2-alpha))
  dsimp [denominatorCap]
  nlinarith only [h1,h2,h3]

theorem slice_kernel_lower (j : Fin 21) {x y : ℝ} (hx : x ∈ Icc alpha beta)
    (hy : y ∈ Ioo (sliceLower j x) (sliceUpper j x)) :
    1/denominatorCap ≤ kernel (profile (basis j)) x y := by
  have hd := slice_domain j hx ⟨hy.1.le, hy.2.le⟩
  change _ ≤ profile (basis j) (u x y) / _
  rw [profile_basis, if_pos (slice_cell j hy)]
  exact one_div_le_one_div_of_le (denominator_bounds hd).1 (denominator_upper hd)

theorem fibre_length_lower (j : Fin 21) {x : ℝ} (hx : x ∈ Icc alpha beta) :
    sliceLength j x / denominatorCap ≤ fibre (basis j) 0 x := by
  have hn : 0 ≤ fibre (basis j) 0 x :=
    intervalIntegral.integral_nonneg (StaircaseShrink.upper_ge (by norm_num) hx.2)
      (fun y hy => kernel_nonneg (basis_nonneg j) ⟨hx,hy⟩)
  by_cases hab : sliceLower j x < sliceUpper j x
  · have ha := le_max_left beta (sumLower j-x)
    have hb : sliceUpper j x ≤ StaircaseShrink.upper 0 x :=
      (slice_domain j hx ⟨hab.le, le_rfl⟩).2.2
    have hi := segment_integrable (basis j) hx ha hab.le hb
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo hab.le
      (intervalIntegrable_const (c := 1/denominatorCap)) hi
      (fun y hy => slice_kernel_lower j hx hy)
    have he := intervalIntegral.integral_mono_interval ha hab.le hb
      (f := kernel (profile (basis j)) x)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact kernel_nonneg (basis_nonneg j) ⟨hx,hy.1.le,hy.2⟩)
      (inner_integrable (basis j) le_rfl (by norm_num) hx)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    rw [sliceLength, max_eq_right (sub_nonneg.mpr hab.le)]
    have hm' : (sliceUpper j x - sliceLower j x) / denominatorCap ≤
        ∫ y in sliceLower j x..sliceUpper j x, kernel (profile (basis j)) x y := by
      simpa only [div_eq_mul_inv, one_mul] using hm
    exact hm'.trans he
  · simpa only [sliceLength, max_eq_left (sub_nonpos.mpr (le_of_not_gt hab)), zero_div]
      using hn

theorem affine_integral (c a b : ℝ) :
    (∫ x in a..b, c-x) = ((c-a)^2-(c-b)^2)/2 := by
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => c) (g := fun x : ℝ => x)
    intervalIntegrable_const
    (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

theorem ramp_integral {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    (∫ x in a..b, max 0 (c-x)) =
      ((max 0 (c-a))^2-(max 0 (c-b))^2)/2 := by
  have hc : Continuous (fun x : ℝ => max 0 (c-x)) := by fun_prop
  by_cases hca : c ≤ a
  · have he : (∫ x in a..b, max 0 (c-x)) = 0 := by
      calc
        _ = ∫ _x in a..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hab] at hx
          exact max_eq_left (by linarith [hx.1])
        _ = 0 := by simp
    rw [he, max_eq_left (sub_nonpos.mpr hca),
      max_eq_left (sub_nonpos.mpr (hca.trans hab))]
    norm_num
  · by_cases hbc : b ≤ c
    · have he : (∫ x in a..b, max 0 (c-x)) = ∫ x in a..b, c-x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        exact max_eq_right (by linarith [hx.2])
      rw [he, affine_integral, max_eq_right (sub_nonneg.mpr (hab.trans hbc)),
        max_eq_right (sub_nonneg.mpr hbc)]
    · have hac : a ≤ c := (lt_of_not_ge hca).le
      have hcb : c ≤ b := (lt_of_not_ge hbc).le
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hc.intervalIntegrable a c) (hc.intervalIntegrable c b)
      have hl : (∫ x in a..c, max 0 (c-x)) = ((c-a)^2)/2 := by
        calc
          _ = ∫ x in a..c, c-x := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le hac] at hx
            exact max_eq_right (sub_nonneg.mpr hx.2)
          _ = _ := by rw [affine_integral]; ring
      have hr : (∫ x in c..b, max 0 (c-x)) = 0 := by
        calc
          _ = ∫ _x in c..b, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le hcb] at hx
            exact max_eq_left (sub_nonpos.mpr hx.1)
          _ = 0 := by simp
      rw [← hsplit, hl, hr, max_eq_right (sub_nonneg.mpr hac),
        max_eq_left (sub_nonpos.mpr hcb)]
      ring

theorem clipped_length_identity {b d t s : ℝ} (hbd : b ≤ d) (hts : t ≤ s) :
    max 0 (min d s - max b t) =
      (max 0 (s-b)-max 0 (s-d))-(max 0 (t-b)-max 0 (t-d)) := by
  rcases le_total s b with hs | hs
  · have ht := hts.trans hs
    rw [min_eq_right (hs.trans hbd), max_eq_left ht,
      max_eq_left (sub_nonpos.mpr hs), max_eq_left (sub_nonpos.mpr (hs.trans hbd)),
      max_eq_left (sub_nonpos.mpr ht), max_eq_left (sub_nonpos.mpr (ht.trans hbd))]
    ring
  · rcases le_total d t with ht | ht
    · rw [min_eq_left (ht.trans hts), max_eq_right (hbd.trans ht),
        max_eq_right (sub_nonneg.mpr hs), max_eq_right (sub_nonneg.mpr (ht.trans hts)),
        max_eq_right (sub_nonneg.mpr (hbd.trans ht)), max_eq_right (sub_nonneg.mpr ht),
        max_eq_left (sub_nonpos.mpr ht)]
      ring
    · rcases le_total s d with hsd | hsd <;> rcases le_total t b with htb | htb
      · rw [min_eq_right hsd, max_eq_left htb, max_eq_right (sub_nonneg.mpr hs),
          max_eq_left (sub_nonpos.mpr hsd), max_eq_left (sub_nonpos.mpr htb),
          max_eq_left (sub_nonpos.mpr ht)]
        ring
      · rw [min_eq_right hsd, max_eq_right htb, max_eq_right (sub_nonneg.mpr hts),
          max_eq_right (sub_nonneg.mpr hs), max_eq_left (sub_nonpos.mpr hsd),
          max_eq_right (sub_nonneg.mpr htb), max_eq_left (sub_nonpos.mpr ht)]
        ring
      · rw [min_eq_left hsd, max_eq_left htb, max_eq_right (sub_nonneg.mpr hbd),
          max_eq_right (sub_nonneg.mpr hs), max_eq_right (sub_nonneg.mpr hsd),
          max_eq_left (sub_nonpos.mpr htb), max_eq_left (sub_nonpos.mpr ht)]
        ring
      · rw [min_eq_left hsd, max_eq_right htb, max_eq_right (sub_nonneg.mpr ht),
          max_eq_right (sub_nonneg.mpr hs), max_eq_right (sub_nonneg.mpr hsd),
          max_eq_right (sub_nonneg.mpr htb), max_eq_left (sub_nonpos.mpr ht)]
        ring

def triangleArea (c : ℝ) : ℝ :=
  ((max 0 (c-alpha-beta))^2 - (max 0 (c-beta-beta))^2 -
    (max 0 (c-alpha-1/4))^2 + (max 0 (c-beta-1/4))^2)/2

def cellArea (j : Fin 21) : ℝ := triangleArea (sumUpper j) - triangleArea (sumLower j)

theorem sliceLength_integral (j : Fin 21) :
    (∫ x in alpha..beta, sliceLength j x) = cellArea j := by
  have he (x : ℝ) : sliceLength j x =
      (max 0 ((sumUpper j-beta)-x) - max 0 ((sumUpper j-1/4)-x)) -
        (max 0 ((sumLower j-beta)-x) - max 0 ((sumLower j-1/4)-x)) := by
    have h := clipped_length_identity (by norm_num [beta] : beta ≤ (1/4 : ℝ))
      (sub_le_sub_right (sum_bounds j).1 x)
    simpa only [sliceLength, sliceLower, sliceUpper, sub_right_comm] using h
  have hi (c : ℝ) : IntervalIntegrable (fun x : ℝ => max 0 (c-x)) volume alpha beta :=
    (by fun_prop : Continuous (fun x : ℝ => max 0 (c-x))).intervalIntegrable _ _
  simp_rw [he]
  rw [intervalIntegral.integral_sub ((hi _).sub (hi _)) ((hi _).sub (hi _)),
    intervalIntegral.integral_sub (hi _) (hi _),
    intervalIntegral.integral_sub (hi _) (hi _)]
  simp only [ramp_integral StaircaseShrink.fixed_bounds.2.1.le]
  unfold cellArea triangleArea
  simp only [sub_right_comm]
  ring

def rationalWeight (j : Fin 21) : ℝ := 4 * cellArea j / denominatorCap

theorem rationalWeight_le (j : Fin 21) : rationalWeight j ≤ weight j := by
  have hc : Continuous (sliceLength j) := by
    unfold sliceLength sliceLower sliceUpper
    fun_prop
  have hm := intervalIntegral.integral_mono_on StaircaseShrink.fixed_bounds.2.1.le
    ((hc.intervalIntegrable _ _).div_const denominatorCap)
    (outer_integrable (basis j) le_rfl (by norm_num))
    (fun x hx => fibre_length_lower j hx)
  rw [intervalIntegral.integral_div, sliceLength_integral] at hm
  rw [weight, Gamma_eq_fibres (basis j) le_rfl (by norm_num)]
  dsimp [rationalWeight]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)

theorem rationalWeight_pos (j : Fin 21) : 0 < rationalWeight j := by
  fin_cases j <;>
    norm_num [rationalWeight, cellArea, triangleArea, sumUpper, sumLower,
      denominatorCap, alpha, beta, rNode]

theorem rational_weights_consumer {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j) :
    (∑ j : Fin 21, rationalWeight j * w j) ≤ Gamma w 0 :=
  lower_weights_consumer rationalWeight_le hw

end
end WuTarget.W03
