import CoupledKernelFTC

namespace CoupledIntegralRecovery
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Interval
noncomputable section

/-- Physical lower endpoint of the unchanged J integral. -/
def jStart (s S : ℝ) : ℝ := S-S/s

/-- A single, non-nested full-profile integral; neither a basis nor a numerical matrix. -/
def jFlat (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  gProfile (nineProfile z) (S-1)*odds S (jStart s S) (S-1) +
    ∫ t in (jStart s S)..(S-1),
      nineProfile z (t-1)/(t-1)*odds S (jStart s S) t

theorem profileJ_physical (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    profileJ z s S = ∫ x in (jStart s S)..(S-1),
      gProfile (nineProfile z) x*(S/(x*(S-x))) := by
  have hS0 : S≠0 := by linarith
  let q : ℝ → ℝ := fun x => gProfile (nineProfile z) x*(S/(x*(S-x)))
  have hc := intervalIntegral.smul_integral_comp_mul_left
    (a := 1-1/s) (b := 1-1/S) q S
  have he1 : S*(1-1/s)=jStart s S := by unfold jStart; ring
  have he2 : S*(1-1/S)=S-1 := by field_simp
  rw [he1,he2] at hc
  change S*(∫ u in (1-1/s)..(1-1/S),q (S*u)) = _ at hc
  rw [← hc, ← intervalIntegral.integral_const_mul]
  unfold profileJ
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (J_geometry hs hS hS5 hsS hr).1] at hu
  have hg := (J_geometry hs hS hS5 hsS hr).2 u hu
  dsimp [q]
  have hu1 : 1-u≠0 := by linarith [hg.2.1]
  field_simp [hS0, hg.1.ne', hu1]

theorem shifted_profile_integrable (z : Fin 9 → ℝ) {a b : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 4) :
    IntervalIntegrable (fun t => nineProfile z (t-1)/(t-1)) volume a b := by
  have hi := profile_div_integrable (nineProfile_integrable z)
  have hj : IntervalIntegrable (fun t => nineProfile z t/t) volume (a-1) (b-1) := by
    apply hi.mono_set
    rw [uIcc_of_le (by linarith : a-1 ≤ b-1),uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    exact Icc_subset_Icc (by linarith) (by linarith)
  convert hj.comp_sub_right 1 using 1 <;> simp

theorem gProfile_tail_split (z : Fin 9 → ℝ) {x b : ℝ}
    (hx : 2 ≤ x) (hxb : x ≤ b) (hb : b ≤ 4) :
    gProfile (nineProfile z) x = gProfile (nineProfile z) b +
      ∫ t in x..b, nineProfile z (t-1)/(t-1) := by
  have hi := profile_div_integrable (nineProfile_integrable z)
  have hxb' : IntervalIntegrable (fun t => nineProfile z t/t) volume (x-1) (b-1) := by
    apply hi.mono_set
    rw [uIcc_of_le (by linarith : x-1 ≤ b-1),uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hb3 := profile_subinterval hi (by linarith : 1 ≤ b-1) (by linarith : b-1 ≤ 3)
  have ha := intervalIntegral.integral_add_adjacent_intervals hxb' hb3
  rw [intervalIntegral.integral_comp_sub_right (fun t => nineProfile z t/t) 1]
  unfold gProfile
  linarith only [ha]

/-- Exact FTC/Fubini elimination of the nested J tail on each genuine admissible row. -/
theorem profileJ_eq_flat (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    profileJ z s S = jFlat z s S := by
  have hstart : 2 ≤ jStart s S := hr
  have hend : jStart s S ≤ S-1 := by
    have hdiv : 1 ≤ S/s := (one_le_div (by linarith : 0<s)).mpr hsS
    unfold jStart
    linarith
  rw [profileJ_physical z hs hS hS5 hsS hr]
  calc
    _ = ∫ x in (jStart s S)..(S-1),
        (gProfile (nineProfile z) (S-1)+
          ∫ t in x..(S-1), nineProfile z (t-1)/(t-1))*(S/(x*(S-x))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hend] at hx
      dsimp only
      rw [gProfile_tail_split z (hstart.trans hx.1) hx.2 (by linarith)]
    _ = _ := odds_full_tail (by linarith : 0<jStart s S) hend (by linarith)
      (shifted_profile_integrable z hstart hend (by linarith)) _

/-- Each of the three literal J terms for every one of the original four coupled rows. -/
theorem coupled_J_flat (z : Fin 9 → ℝ) (i : Fin 4) :
    profileJ z (coupledRow i).s (coupledRow i).S = jFlat z (coupledRow i).s (coupledRow i).S ∧
    profileJ z (coupledRow i).kappa2 (coupledRow i).S = jFlat z (coupledRow i).kappa2 (coupledRow i).S ∧
    profileJ z (coupledRow i).kappa3 (coupledRow i).S = jFlat z (coupledRow i).kappa3 (coupledRow i).S := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  exact ⟨profileJ_eq_flat z hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1,
    profileJ_eq_flat z hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1,
    profileJ_eq_flat z hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.2.2.1 hp.2.2.2.2⟩

end
end CoupledIntegralRecovery
