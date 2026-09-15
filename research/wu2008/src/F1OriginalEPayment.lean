import F1SecondLogExtent

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence Wu08OriginalFirstSteps
open scoped Interval
namespace F1OriginalEPayment

theorem polynomial_integral (c a b : ℝ) (n : ℕ) :
    (∫ u in a..b,c*(u-a)^n)=c*(b-a)^(n+1)/(n+1:ℕ) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => c*(u-a)^(n+1)/(n+1:ℕ)) (c*(u-a)^n) u := by
    have h := ((((hasDerivAt_id u).sub_const a).pow (n+1)).const_mul c).div_const (n+1:ℕ)
    convert h using 1 <;> first | rfl | skip
    dsimp
    have hn : ((n+1:ℕ):ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
  have hc : Continuous (fun u : ℝ => c*(u-a)^n) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hc.intervalIntegrable a b)]
  simp

theorem log_linear {v : ℝ} (hv : 2 ≤ v) : 2*(v-2)/v ≤ log (v-1) := by
  have hl := log_lower (by linarith : 1 ≤ v-1)
  have hq : 0 ≤ (v-2)/v := div_nonneg (by linarith) (by linarith)
  have hh : 0 ≤ 2*((v-2)/v)^3/3 := by positivity
  unfold lowerLog at hl
  rw [show v-1-1=v-2 by ring,show v-1+1=v by ring] at hl
  simp only [mul_div_assoc]
  linarith only [hl,hh]

theorem B_lower {s : ℝ} (hs : 3 ≤ s) : (s-3)^2/(s-1)^2 ≤ B s := by
  have hh (v : ℝ) (hv : v∈Icc 2 (s-1)) :
      (2/(s-1)^2)*(v-2) ≤ k v := by
    have hv0 : 0<v := by linarith [hv.1]
    have hd : v^2 ≤ (s-1)^2 := by gcongr; exact hv.2
    have h1 := div_le_div_of_nonneg_left (by linarith [hv.1] : 0 ≤ 2*(v-2)) (sq_pos_of_pos hv0) hd
    have h2 := div_le_div_of_nonneg_right (log_linear hv.1) hv0.le
    rw [k_literal hv.1]
    rw [div_div] at h2
    have hvv : v*v=v^2 := by ring
    rw [hvv] at h2
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using h1.trans h2
  have hc : Continuous (fun v : ℝ => (2/(s-1)^2)*(v-2)) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (2:ℝ) ≤ s-1)
    (hc.intervalIntegrable 2 (s-1)) (k_continuous.intervalIntegrable 2 (s-1)) hh
  have he := polynomial_integral (2/(s-1)^2) 2 (s-1) 1
  norm_num only [pow_one] at he
  rw [he] at h
  unfold B
  convert h using 1
  ring

theorem C_lower {s : ℝ} (hs : 4 ≤ s) :
    (s-4)^3/(3*(s-2)^2*(s-1)) ≤ C s := by
  have hh (v : ℝ) (hv : v∈Icc 3 (s-1)) :
      (1/((s-2)^2*(s-1)))*(v-3)^2 ≤ B v/max 1 v := by
    have hv0 : 0<v := by linarith [hv.1]
    have hvd : 0 ≤ v-3 := sub_nonneg.mpr hv.1
    have hv1 : 0<v-1 := by linarith [hv.1]
    have hs1 : 0<s-1 := by linarith
    have hs2 : 0<s-2 := by linarith
    have hd0 : 0<((v-1)^2)*v := by
      have hvlo := hv.1
      positivity
    have hd : ((v-1)^2)*v ≤ (s-2)^2*(s-1) := by
      apply mul_le_mul _ hv.2 hv0.le (by positivity)
      exact pow_le_pow_left₀ hv1.le (by linarith [hv.2]) 2
    have h1 := div_le_div_of_nonneg_left (by positivity : 0 ≤ (v-3)^2) hd0 hd
    have h2 := div_le_div_of_nonneg_right (B_lower hv.1) hv0.le
    rw [div_div] at h2
    rw [max_eq_right (by linarith [hv.1] : (1:ℝ) ≤ v)]
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using h1.trans h2
  have hc : Continuous (fun v : ℝ => (1/((s-2)^2*(s-1)))*(v-3)^2) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (3:ℝ) ≤ s-1)
    (hc.intervalIntegrable 3 (s-1))
    ((div_continuous B_continuous).intervalIntegrable 3 (s-1)) hh
  rw [polynomial_integral (1/((s-2)^2*(s-1))) 3 (s-1) 2] at h
  unfold C
  convert h using 1
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem D_lower {s : ℝ} (hs : 5 ≤ s) :
    (s-5)^4/(12*(s-3)^2*(s-2)*(s-1)) ≤ D s := by
  have hh (v : ℝ) (hv : v∈Icc 4 (s-1)) :
      (1/(3*(s-3)^2*(s-2)*(s-1)))*(v-4)^3 ≤ C v/max 1 v := by
    have hv0 : 0<v := by linarith [hv.1]
    have hvd : 0 ≤ v-4 := sub_nonneg.mpr hv.1
    have hv1 : 0<v-1 := by linarith [hv.1]
    have hv2 : 0<v-2 := by linarith [hv.1]
    have hs1 : 0<s-1 := by linarith
    have hs2 : 0<s-2 := by linarith
    have hs3 : 0<s-3 := by linarith
    have hd0 : 0<(3*(v-2)^2*(v-1))*v := by
      have hvlo := hv.1
      positivity
    have hd : (3*(v-2)^2*(v-1))*v ≤ 3*(s-3)^2*(s-2)*(s-1) := by
      apply mul_le_mul _ hv.2 hv0.le (by positivity)
      apply mul_le_mul _ (by linarith [hv.2] : v-1 ≤ s-2) hv1.le (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ hv2.le (by linarith [hv.2]) 2
    have h1 := div_le_div_of_nonneg_left (by positivity : 0 ≤ (v-4)^3) hd0 hd
    have h2 := div_le_div_of_nonneg_right (C_lower hv.1) hv0.le
    rw [div_div] at h2
    rw [max_eq_right (by linarith [hv.1] : (1:ℝ) ≤ v)]
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using h1.trans h2
  have hc : Continuous (fun v : ℝ => (1/(3*(s-3)^2*(s-2)*(s-1)))*(v-4)^3) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (4:ℝ) ≤ s-1)
    (hc.intervalIntegrable 4 (s-1))
    ((div_continuous C_continuous).intervalIntegrable 4 (s-1)) hh
  rw [polynomial_integral (1/(3*(s-3)^2*(s-2)*(s-1))) 4 (s-1) 3] at h
  unfold D
  convert h using 1
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem E_lower {s : ℝ} (hs : 6 ≤ s) :
    (s-6)^5/(60*(s-4)^2*(s-3)*(s-2)*(s-1)) ≤ E s := by
  have hh (v : ℝ) (hv : v∈Icc 5 (s-1)) :
      (1/(12*(s-4)^2*(s-3)*(s-2)*(s-1)))*(v-5)^4 ≤ D v/max 1 v := by
    have hv0 : 0<v := by linarith [hv.1]
    have hvd : 0 ≤ v-5 := sub_nonneg.mpr hv.1
    have hv1 : 0<v-1 := by linarith [hv.1]
    have hv2 : 0<v-2 := by linarith [hv.1]
    have hv3 : 0<v-3 := by linarith [hv.1]
    have hs1 : 0<s-1 := by linarith
    have hs2 : 0<s-2 := by linarith
    have hs3 : 0<s-3 := by linarith
    have hs4 : 0<s-4 := by linarith
    have hd0 : 0<(12*(v-3)^2*(v-2)*(v-1))*v := by
      have hvlo := hv.1
      positivity
    have hd : (12*(v-3)^2*(v-2)*(v-1))*v ≤ 12*(s-4)^2*(s-3)*(s-2)*(s-1) := by
      apply mul_le_mul _ hv.2 hv0.le (by positivity)
      apply mul_le_mul _ (by linarith [hv.2] : v-1 ≤ s-2) hv1.le (by positivity)
      apply mul_le_mul _ (by linarith [hv.2] : v-2 ≤ s-3) hv2.le (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ hv3.le (by linarith [hv.2]) 2
    have h1 := div_le_div_of_nonneg_left (by positivity : 0 ≤ (v-5)^4) hd0 hd
    have h2 := div_le_div_of_nonneg_right (D_lower hv.1) hv0.le
    rw [div_div] at h2
    rw [max_eq_right (by linarith [hv.1] : (1:ℝ) ≤ v)]
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using h1.trans h2
  have hc : Continuous (fun v : ℝ => (1/(12*(s-4)^2*(s-3)*(s-2)*(s-1)))*(v-5)^4) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (5:ℝ) ≤ s-1)
    (hc.intervalIntegrable 5 (s-1))
    ((div_continuous D_continuous).intervalIntegrable 5 (s-1)) hh
  rw [polynomial_integral (1/(12*(s-4)^2*(s-3)*(s-2)*(s-1))) 5 (s-1) 4] at h
  unfold E
  convert h using 1
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end F1OriginalEPayment
