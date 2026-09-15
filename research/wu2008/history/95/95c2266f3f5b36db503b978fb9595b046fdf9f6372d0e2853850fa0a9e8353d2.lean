import W05JCoefficients

noncomputable section
namespace WuTarget.W05
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment
open scoped Interval BigOperators

theorem elementary_le_lowerLog {x : ℝ} (hx : 1 ≤ x) :
    (x - 1) / x ≤ SharpLogRecurrence.lowerLog x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) hx1.le
  have he : 2 * ((x - 1) / (x + 1)) - (x - 1) / x =
      (x - 1) ^ 2 / (x * (x + 1)) := by
    field_simp
    ring
  have hn : 0 ≤ (x - 1) ^ 2 / (x * (x + 1)) := by positivity
  have hc : 0 ≤ 2 * ((x - 1) / (x + 1)) ^ 3 / 3 := by positivity
  unfold SharpLogRecurrence.lowerLog
  linarith only [he, hn, hc]

def rationalCell (S A a b : ℝ) : ℝ :=
  (b - a) * (a + b - 2 * (A - 1)) / 2 *
    (1 / (b * (b + 1)) + 1 / (b * (S - A)))

theorem rationalCell_nonneg {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S - 1)
    (ha : A - 1 ≤ a) (hab : a ≤ b) :
    0 ≤ rationalCell S A a b := by
  have hb : 0 < b := by linarith
  have hC : 0 < S - A := by linarith
  have hw : 0 ≤ a + b - 2 * (A - 1) := by linarith
  have hd : 0 ≤ b - a := by linarith
  unfold rationalCell
  positivity

theorem rationalKernel_le {S A b u : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S - 1)
    (hu : A - 1 ≤ u) (hub : u ≤ b) (hb : b ≤ S - 2) :
    (u - (A - 1)) * (1 / (b * (b + 1)) + 1 / (b * (S - A))) ≤
      CoupledJLogRecovery.kernel S A u := by
  have hu0 : 0 < u := by linarith
  have hb0 : 0 < b := hu0.trans_le hub
  have hA0 : 0 < A := by linarith
  have hC : 0 < S - A := by linarith
  have hD : 0 < S - 1 - u := by linarith
  have hx : 1 ≤ (u + 1) / A := (one_le_div hA0).mpr (by linarith)
  have hy : 1 ≤ (S - A) / (S - 1 - u) := (one_le_div hD).mpr (by linarith)
  have he1 : (((u + 1) / A) - 1) / ((u + 1) / A) =
      (u - (A - 1)) / (u + 1) := by field_simp; ring
  have he2 : (((S - A) / (S - 1 - u)) - 1) / ((S - A) / (S - 1 - u)) =
      (u - (A - 1)) / (S - A) := by field_simp; ring
  have h1 := elementary_le_lowerLog hx
  have h2 := elementary_le_lowerLog hy
  rw [he1] at h1
  rw [he2] at h2
  have hn : 0 ≤ u - (A - 1) := by linarith
  have hd1 : u * (u + 1) ≤ b * (b + 1) :=
    mul_le_mul hub (by linarith) (by linarith) hb0.le
  have hd2 : u * (S - A) ≤ b * (S - A) :=
    mul_le_mul_of_nonneg_right hub hC.le
  have h3 := div_le_div_of_nonneg_left hn (mul_pos hu0 (by linarith)) hd1
  have h4 := div_le_div_of_nonneg_left hn (mul_pos hu0 hC) hd2
  have hj : (u - (A - 1)) * (1 / (b * (b + 1)) + 1 / (b * (S - A))) ≤
      jKernel S A u := by
    rw [jKernel_eq hA hAS ⟨hu, hub.trans hb⟩]
    have h5 := div_le_div_of_nonneg_right (add_le_add h1 h2) hu0.le
    simp only [add_div, div_div] at h5
    rw [mul_comm (u + 1) u, mul_comm (S - A) u] at h5
    calc
      _ = (u - (A - 1)) / (b * (b + 1)) +
          (u - (A - 1)) / (b * (S - A)) := by ring
      _ ≤ _ := (add_le_add h3 h4).trans h5
  have h6 := CoupledJLogRecovery.firstError_nonneg hA hu
  have h7 := CoupledJLogRecovery.secondError_nonneg hA hAS ⟨hu, hub.trans hb⟩
  unfold CoupledJLogRecovery.kernel
  linarith only [hj, h6, h7]

theorem rationalCell_le {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S - 1)
    (ha : A - 1 ≤ a) (hab : a ≤ b) (hb : b ≤ S - 2) :
    rationalCell S A a b ≤
      CoupledJLogRecovery.fullPrimitive S A b - CoupledJLogRecovery.fullPrimitive S A a := by
  let c : ℝ := 1 / (b * (b + 1)) + 1 / (b * (S - A))
  have hi : IntervalIntegrable (fun u : ℝ => (u - (A - 1)) * c) volume a b :=
    (by fun_prop : Continuous (fun u : ℝ => (u - (A - 1)) * c)).intervalIntegrable a b
  have hd (u : ℝ) : HasDerivAt (fun t : ℝ => (t ^ 2 / 2 - (A - 1) * t) * c)
      ((u - (A - 1)) * c) u := by
    convert ((((hasDerivAt_id u).pow 2).div_const (2 : ℝ)).sub
      ((hasDerivAt_id u).const_mul (A - 1))).mul_const c using 1 <;> norm_num <;> rfl
  have he : (∫ u in a..b, (u - (A - 1)) * c) = rationalCell S A a b := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
    unfold rationalCell c
    ring
  rw [← he, ← CoupledJLogRecovery.kernel_integral hA hAS ha hab hb]
  exact intervalIntegral.integral_mono_on hab hi
    (CoupledJLogRecovery.kernel_continuous hA hAS ha hab hb).intervalIntegrable
    (fun u hu => rationalKernel_le hA hAS (ha.trans hu.1) hu.2 hb)

def rationalJCoefficient (s S : ℝ) (k : Fin 9) : ℝ :=
  ((right (S - 2) 3 k - left (S - 2) 3 k) / right (S - 2) 3 k) *
      ((S - s) / (S - 1)) +
    rationalCell S (jStart s S)
      (left (jStart s S - 1) (S - 2) k) (right (jStart s S - 1) (S - 2) k)

theorem endpoint_log_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [log_div ha.ne' hb.ne'] at h
  rw [log_div hb.ne' ha.ne']
  have he : (b - a) / b = 1 - a / b := by field_simp
  rw [he]
  linarith only [h]

theorem rationalJCoefficient_le {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S)
    (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S - S / s) (k : Fin 9) :
    rationalJCoefficient s S k ≤ jCoefficient s S k := by
  have hA := jStart_bounds hs hsS hr
  have hab : jStart s S - 1 ≤ S - 2 := by linarith [hA.2]
  have ht : S - 2 ≤ (3 : ℝ) := by linarith
  have hl : 0 < left (S - 2) 3 k := by
    have h := (clip_bounds (x := upperLeft k) ht).1
    change S - 2 ≤ left (S - 2) 3 k at h
    linarith
  have hc := cell_order (S - 2) 3 k
  have h1 := endpoint_log_lower hl hc
  have h2 := endpoint_log_lower (by linarith : 0 < s - 1)
    (by linarith : s - 1 ≤ S - 1)
  have he : (S - 1 - (s - 1)) / (S - 1) = (S - s) / (S - 1) := by ring
  rw [he] at h2
  have hn : 0 ≤ (S - s) / (S - 1) := div_nonneg (by linarith) (by linarith)
  have hm := mul_le_mul h1 h2 hn
    (log_nonneg ((one_le_div hl).mpr hc))
  exact add_le_add hm (rationalCell_le
    (a := left (jStart s S - 1) (S - 2) k)
    (b := right (jStart s S - 1) (S - 2) k)
    hA.1 hA.2 (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2)

theorem rationalJCoefficient_nonneg {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S)
    (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S - S / s) (k : Fin 9) :
    0 ≤ rationalJCoefficient s S k := by
  have hA := jStart_bounds hs hsS hr
  have hab : jStart s S - 1 ≤ S - 2 := by linarith [hA.2]
  have ht : S - 2 ≤ (3 : ℝ) := by linarith
  have hl : 0 < right (S - 2) 3 k := by
    have h := (clip_bounds (x := upperNode k) ht).1
    change S - 2 ≤ right (S - 2) 3 k at h
    linarith
  apply add_nonneg
  · exact mul_nonneg
      (div_nonneg (sub_nonneg.mpr (cell_order _ _ k)) hl.le)
      (div_nonneg (sub_nonneg.mpr hsS) (by linarith))
  · exact rationalCell_nonneg hA.1 hA.2 (clip_bounds hab).1 (cell_order _ _ k)

theorem rationalJCoefficients_paid {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    aProfile (nineProfile z) * log ((S - 1) / (s - 1)) +
      ∑ k : Fin 9, rationalJCoefficient s S k * z k ≤ profileJ z s S := by
  apply le_trans _ (jCoefficients_paid hz hs hS hS5 hsS hr)
  exact add_le_add_left (Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (rationalJCoefficient_le hs hS hS5 hsS hr k) (hz k))) _

theorem rational_terminal_zero (k : Fin 9) : rationalJCoefficient 3 3 k = 0 := by
  norm_num [rationalJCoefficient, rationalCell, jStart, left, right, clip]

end WuTarget.W05
