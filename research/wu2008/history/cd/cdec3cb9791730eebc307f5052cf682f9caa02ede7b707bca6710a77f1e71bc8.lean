import W03Area

namespace WuTarget.W03
open Set MeasureTheory QuarterTrim DirectFiniteF6 NodeExtension Wu2008DoubleSieve
open scoped Classical
noncomputable section

theorem cell_sum_iff (j : Fin 21) (x y : ℝ) :
    cell j (u x y) ↔ sumLower j ≤ x+y ∧ x+y < sumUpper j := by
  unfold cell u
  rw [lt_div_iff₀ alpha_pos, div_le_iff₀ alpha_pos]
  unfold sumLower sumUpper
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem uniform_slice_support (j : Fin 21) (x : ℝ) :
    Function.support (fun y => uniform (basis j) 0 (x,y)) ⊆
      Icc (sliceLower j x) (sliceUpper j x) := by
  intro y hy
  by_cases h : (x,y) ∈ StaircaseShrink.domain 0 ∧ cell j (u x y)
  · have hs := (cell_sum_iff j x y).mp h.2
    have hd := (StaircaseShrink.domain_iff 0 x y).mp h.1
    exact ⟨max_le hd.2.2.1 (by linarith),
      le_min (by linarith [hd.2.2.2.1]) (by linarith)⟩
  · exact False.elim (hy (by simp only [uniform_basis, if_neg h]))

theorem fibre_eq_uniform_integral (j : Fin 21) {x : ℝ} (hx : x ∈ Icc alpha beta) :
    fibre (basis j) 0 x = ∫ y : ℝ, uniform (basis j) 0 (x,y) := by
  have hs : Function.support (fun y => uniform (basis j) 0 (x,y)) ⊆
      Icc beta (StaircaseShrink.upper 0 x) := by
    intro y hy
    by_contra hn
    exact hy (by simp [uniform, StaircaseShrink.domain, hn])
  rw [truncatedSixthMass_integral_eq_interval
    (StaircaseShrink.upper_ge (by norm_num) hx.2) hs]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (StaircaseShrink.upper_ge (by norm_num) hx.2)] at hy
  exact (if_pos (show (x,y) ∈ StaircaseShrink.domain 0 from ⟨hx,hy⟩)).symm

def reciprocalKernel (x y : ℝ) : ℝ := 1 / (x*y*(1/2-x-y))

theorem fibre_clipped (j : Fin 21) {x : ℝ} (hx : x ∈ Icc alpha beta) :
    fibre (basis j) 0 x =
      if sliceLower j x ≤ sliceUpper j x then
        ∫ y in sliceLower j x..sliceUpper j x, reciprocalKernel x y else 0 := by
  rw [fibre_eq_uniform_integral j hx]
  by_cases h : sliceLower j x ≤ sliceUpper j x
  · rw [if_pos h, truncatedSixthMass_integral_eq_interval h (uniform_slice_support j x)]
    apply intervalIntegral.integral_congr_uIoo
    intro y hy
    rw [uIoo_of_le h] at hy
    rw [uniform_basis, if_pos ⟨slice_domain j hx ⟨hy.1.le,hy.2.le⟩, slice_cell j hy⟩]
    rfl
  · rw [if_neg h]
    have he : (fun y => uniform (basis j) 0 (x,y)) = 0 := by
      funext y
      by_contra hn
      have hy := uniform_slice_support j x hn
      exact h (hy.1.trans hy.2)
    rw [he]
    simp

def logPrimitive (x y : ℝ) : ℝ :=
  (Real.log y - Real.log (1/2-x-y)) / (x*(1/2-x))

theorem logPrimitive_derivative {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < 1/2-x-y) :
    HasDerivAt (logPrimitive x) (reciprocalKernel x y) y := by
  have hc : 0 < 1/2-x := by linarith
  have h1 := (hasDerivAt_id y).log hy.ne'
  have h2 := ((hasDerivAt_const y (1/2-x)).sub (hasDerivAt_id y)).log hz.ne'
  convert (h1.sub h2).div_const (x*(1/2-x)) using 1
  dsimp [reciprocalKernel]
  field_simp
  <;> ring

theorem reciprocal_slice_integral (j : Fin 21) {x : ℝ} (hx : x ∈ Icc alpha beta)
    (h : sliceLower j x ≤ sliceUpper j x) :
    (∫ y in sliceLower j x..sliceUpper j x, reciprocalKernel x y) =
      logPrimitive x (sliceUpper j x) - logPrimitive x (sliceLower j x) := by
  have hd (y : ℝ) (hy : y ∈ uIcc (sliceLower j x) (sliceUpper j x)) :
      (x,y) ∈ StaircaseShrink.domain 0 := by
    rw [uIcc_of_le h] at hy
    exact slice_domain j hx hy
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    have hv := hd y hy
    have hz := (StaircaseShrink.domain_iff 0 x y).mp hv
    apply logPrimitive_derivative (alpha_pos.trans_le hx.1)
      (StaircaseShrink.fixed_bounds.1.trans_le hv.2.1)
    linarith [hz.2.2.2.2, alpha_pos]
  · apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (by fun_prop)
      (fun y hy => (denominator_bounds (hd y hy)).1.ne')

def logSlice (j : Fin 21) (x : ℝ) : ℝ :=
  if sliceLower j x ≤ sliceUpper j x then
    logPrimitive x (sliceUpper j x) - logPrimitive x (sliceLower j x) else 0

theorem fibre_logSlice (j : Fin 21) {x : ℝ} (hx : x ∈ Icc alpha beta) :
    fibre (basis j) 0 x = logSlice j x := by
  rw [fibre_clipped j hx]
  unfold logSlice
  split_ifs with h
  · exact reciprocal_slice_integral j hx h
  · rfl

theorem logSlice_integrable (j : Fin 21) :
    IntervalIntegrable (logSlice j) volume alpha beta := by
  apply (outer_integrable (basis j) le_rfl (by norm_num)).congr
  intro x hx
  rw [uIoc_of_le StaircaseShrink.fixed_bounds.2.1.le] at hx
  exact fibre_logSlice j ⟨hx.1.le,hx.2⟩

theorem weight_one_dimensional (j : Fin 21) :
    weight j = 4 * ∫ x in alpha..beta, logSlice j x := by
  rw [weight, Gamma_eq_fibres (basis j) le_rfl (by norm_num)]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le StaircaseShrink.fixed_bounds.2.1.le] at hx
  exact fibre_logSlice j hx

end
end WuTarget.W03
