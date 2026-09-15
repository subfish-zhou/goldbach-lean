import MathlibNt.Wu2008DoubleSieve.FourRoughDensityRegularity

namespace Wu2008DoubleSieve.FourRoughClosedMass
open Set Real MeasureTheory
noncomputable section

theorem J3_bound (e : Bool) (x y z : ℝ) : |J3 e x y z| ≤ 60 := by
  simpa only [J3, show (4 : ℝ)*15 = 60 by norm_num] using
    low_integral_bound_four (lower_low e z) (upper_low e z) (by norm_num : (0 : ℝ) ≤ 15)
    (fun t _ => F_bound x y z t)

theorem J3_first (e : Bool) {y z : ℝ} (hy : y ∈ low) (hz : z ∈ low) :
    lip 28800 (fun x => J3 e x y z) := by
  intro x hx x' hx'
  have h := low_integral_sub (low_continuous (F_fourth hx hy hz))
    (low_continuous (F_fourth hx' hy hz)) (lower_low e z) (upper_low e z)
    (show 0 ≤ 7200*|x-x'| by positivity)
    (fun t ht => F_first hy hz ht x hx x' hx')
  change |J3 e x y z-J3 e x' y z| ≤ _ at h
  linarith only [h]

theorem J3_second (e : Bool) {x z : ℝ} (hx : x ∈ low) (hz : z ∈ low) :
    lip 28800 (fun y => J3 e x y z) := by
  intro y hy y' hy'
  have h := low_integral_sub (low_continuous (F_fourth hx hy hz))
    (low_continuous (F_fourth hx hy' hz)) (lower_low e z) (upper_low e z)
    (show 0 ≤ 7200*|y-y'| by positivity)
    (fun t ht => F_second hx hz ht y hy y' hy')
  change |J3 e x y z-J3 e x y' z| ≤ _ at h
  linarith only [h]

theorem J3_third (e : Bool) {x y : ℝ} (hx : x ∈ low) (hy : y ∈ low) :
    lip 29250 (J3 e x y) := by
  have h := (low_moving_lip (M := 15) (K := 7200) (by norm_num) (by norm_num)
    (fun z hz => low_continuous (F_fourth hx hy hz))
    (fun z _ t _ => F_bound x y z t)
    (fun z hz z' hz' t ht => F_third hx hy ht z hz z' hz')
    (fun z _ => lower_low e z) (fun z _ => upper_low e z) (lower_lip e) (upper_lip e)).2
  norm_num only at h
  exact h

theorem J2_bound (e : Bool) (x y : ℝ) : |J2 e x y| ≤ 240 := by
  simpa only [J2, show (4 : ℝ)*60 = 240 by norm_num] using
    low_integral_bound_four (cap_low y) beta_low (by norm_num : (0 : ℝ) ≤ 60)
    (fun z _ => J3_bound e x y z)

theorem J2_first (e : Bool) {y : ℝ} (hy : y ∈ low) :
    lip 115200 (fun x => J2 e x y) := by
  intro x hx x' hx'
  have h := low_integral_sub (low_continuous (J3_third e hx hy))
    (low_continuous (J3_third e hx' hy)) (cap_low y) beta_low
    (show 0 ≤ 28800*|x-x'| by positivity)
    (fun z hz => J3_first e hy hz x hx x' hx')
  change |J2 e x y-J2 e x' y| ≤ _ at h
  linarith only [h]

theorem J2_second (e : Bool) {x : ℝ} (hx : x ∈ low) :
    lip 116100 (J2 e x) := by
  have h := (low_moving_lip (M := 60) (K := 28800) (L := 1) (U := 0)
    (by norm_num) (by norm_num)
    (fun y hy => low_continuous (J3_third e hx hy))
    (fun y _ z _ => J3_bound e x y z)
    (fun y hy y' hy' z hz => J3_second e hx hz y hy y' hy')
    (fun y _ => cap_low y) (fun _ _ => beta_low) cap_lip
    (show lip 0 (fun _ => beta) by intro x _ y _; simp)).2
  norm_num only at h
  exact h

theorem J1_bound (e : Bool) (x : ℝ) : |J1 e x| ≤ 960 := by
  simpa only [J1, show (4 : ℝ)*240 = 960 by norm_num] using
    low_integral_bound_four (cap_low x) beta_low (by norm_num : (0 : ℝ) ≤ 240)
    (fun y _ => J2_bound e x y)

theorem J1_lip (e : Bool) : lip 464400 (J1 e) := by
  have h := (low_moving_lip (M := 240) (K := 115200) (L := 1) (U := 0)
    (by norm_num) (by norm_num)
    (fun x hx => low_continuous (J2_second e hx))
    (fun x _ y _ => J2_bound e x y)
    (fun x hx x' hx' y hy => J2_first e hy x hx x' hx')
    (fun x _ => cap_low x) (fun _ _ => beta_low) cap_lip
    (show lip 0 (fun _ => beta) by intro x _ y _; simp)).2
  norm_num only at h
  exact h

end
end Wu2008DoubleSieve.FourRoughClosedMass
