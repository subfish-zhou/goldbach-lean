import F1SecondLogRetained

noncomputable section
open Real Set FirstIntegralRecovery Wu2008DoubleSieve SharpLogRecurrence
open F1UnpaidRecovery
namespace F1SecondLogRecovery

def weight (u : ℝ) : ℝ := (u-2)*(927/200-u)^5

def errorDenomOne (u : ℝ) : ℝ :=
  (1127/200+3*(u+1))^3*((1127/200)^2+18*(1127/200)*(u+1)+21*(u+1)^2)

def errorDenomTwo (u : ℝ) : ℝ :=
  (3*(1127/200)+(u+1))^3*(21*(1127/200)^2+18*(1127/200)*(u+1)+(u+1)^2)

def denomOne (u : ℝ) : ℝ := (u+2)*(3*u-2)*errorDenomOne u

def denomTwo (u : ℝ) : ℝ := (u+2)*(3*u-2)*errorDenomTwo u

theorem denominators_pos {u : ℝ} (hu : 2 ≤ u) :
    0 < errorDenomOne u ∧ 0 < errorDenomTwo u ∧ 0 < denomOne u ∧ 0 < denomTwo u := by
  have hu0 : 0 < u := by linarith
  have ht : 0 < 3*u-2 := by linarith
  unfold denomOne denomTwo errorDenomOne errorDenomTwo
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

theorem both_errors_generic {r : ℝ} (hr : 1 ≤ r) :
    (r-1)^5/((r+3)^3*(r^2+18*r+21))+
      (r-1)^5/((3*r+1)^3*(21*r^2+18*r+1)) ≤ log r-splitL r := by
  have h := both_split_errors (show 2 ≤ r+1 by linarith)
  convert h using 1 <;> ring_nf

theorem scaled_error_one {k v : ℝ} (hk : 0 < k) (hv : 0 < v) :
    (k/v-1)^5/((k/v+3)^3*((k/v)^2+18*(k/v)+21)) =
      (k-v)^5/((k+3*v)^3*(k^2+18*k*v+21*v^2)) := by
  have hr : 0 < k/v := div_pos hk hv
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  field_simp

theorem scaled_error_two {k v : ℝ} (hk : 0 < k) (hv : 0 < v) :
    (k/v-1)^5/((3*(k/v)+1)^3*(21*(k/v)^2+18*(k/v)+1)) =
      (k-v)^5/((3*k+v)^3*(21*k^2+18*k*v+v^2)) := by
  have hr : 0 < k/v := div_pos hk hv
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  field_simp

/-- Consume exactly the two factors of B's existing once-only split. -/
theorem second_errors {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (927/200-u)^5/errorDenomOne u+(927/200-u)^5/errorDenomTwo u ≤
      log (((1327:ℝ)/200-1)/(u+1))-splitL (((1327:ℝ)/200-1)/(u+1)) := by
  have hu' : u ∈ Icc 2 ((1327:ℝ)/200-2) := by constructor <;> linarith [hu.1,hu.2]
  have h := both_errors_generic (ratio_ge_one hu')
  norm_num only [show (1327:ℝ)/200-1 = 1127/200 by norm_num] at h ⊢
  rw [scaled_error_one (by norm_num) (by linarith [hu.1]),
    scaled_error_two (by norm_num) (by linarith [hu.1])] at h
  convert h using 1
  unfold errorDenomOne errorDenomTwo
  ring

/-- Exact rational payment belonging solely to the previously unpaid second log. -/
theorem second_rational_lower {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    8*weight u/denomOne u+8*weight u/denomTwo u ≤ secondExact u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have ht : 0 < 3*u-2 := by linarith [hu.1]
  obtain ⟨hd1,hd2,_,_⟩ := denominators_pos hu.1
  have hnonneg : 0 ≤ (927/200-u)^5/errorDenomOne u+(927/200-u)^5/errorDenomTwo u := by
    have hd : 0 ≤ 927/200-u := by linarith [hu.2]
    positivity
  have hLA : 0 ≤ splitL (u-1)/u :=
    div_nonneg (splitL_nonneg (by linarith [hu.1])) hu0.le
  have h := mul_le_mul (div_le_div_of_nonneg_right (splitL_linear hu.1) hu0.le)
    (second_errors hu) hnonneg hLA
  have heq : ((2*(u-2)/(u+2)+2*(u-2)/(3*u-2))/u)*
      ((927/200-u)^5/errorDenomOne u+(927/200-u)^5/errorDenomTwo u) =
      8*weight u/denomOne u+8*weight u/denomTwo u := by
    unfold denomOne denomTwo weight
    field_simp [ht.ne',hu0.ne',hd1.ne',hd2.ne',show u+2 ≠ 0 by linarith [hu.1]]
    ring_nf
    field_simp [show -2+u*3 ≠ 0 by linarith [hu.1]]
    ring
  rw [heq] at h
  exact h

end F1SecondLogRecovery
