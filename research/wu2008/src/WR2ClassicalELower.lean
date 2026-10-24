import WR2ClassicalPolynomialLower

noncomputable section
namespace WuPaper.ClassicalE
open Real Set MeasureTheory Wu08OriginalFirstSteps ClassicalPolynomial
open scoped Interval

def S : ℝ := 1327/200
def base : ℝ := 1/((S-5)*(S-4))
def bCoef : ℝ := base/2
def cCoef : ℝ := bCoef/(S-3)/3
def dCoef : ℝ := cCoef/(S-2)/4

theorem k_lower {v : ℝ} (hv : 2 ≤ v) (hvS : v ≤ S-4) : base*(v-2) ≤ k v := by
  have hv0 : 0 < v := by linarith
  have hv1 : 0 < v-1 := by linarith
  have hlog : (v-2)/(S-5) ≤ log (v-1) := by
    calc
      _ ≤ (v-2)/(v-1) := div_le_div_of_nonneg_left (by linarith) hv1 (by linarith)
      _ = 1-(v-1)⁻¹ := by field_simp; ring
      _ ≤ _ := one_sub_inv_le_log_of_pos hv1
  have h := div_le_div₀ (log_nonneg (by linarith : 1 ≤ v-1)) hlog hv0 hvS
  rw [k_literal hv]
  calc
    base*(v-2) = (v-2)/(S-5)/(S-4) := by
      simp only [base,div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := h

theorem B_lower {x : ℝ} (hx : 3 ≤ x) (hxS : x ≤ S-3) : bCoef*(x-3)^2 ≤ B x := by
  have h := integral_lower (f := k) (a := 2) (b := x-1) (c := base) 1
    (by linarith) (k_continuous.intervalIntegrable 2 (x-1))
    (fun v hv => by simpa only [pow_one] using k_lower hv.1 (by linarith [hv.2]))
  change _ ≤ B x at h
  convert h using 1; dsimp [bCoef]; ring

theorem C_lower {x : ℝ} (hx : 4 ≤ x) (hxS : x ≤ S-2) : cCoef*(x-4)^3 ≤ C x := by
  have h := divided_integral_lower (f := B) (a := 3) (b := x-1) (c := bCoef) (R := S-3) 2
    (by norm_num) (by linarith) (by linarith) (by norm_num [bCoef,base,S]) B_continuous
    (fun v hv => B_lower hv.1 (by linarith [hv.2]))
  change _ ≤ C x at h
  convert h using 1; dsimp [cCoef]; ring

theorem D_lower {x : ℝ} (hx : 5 ≤ x) (hxS : x ≤ S-1) : dCoef*(x-5)^4 ≤ D x := by
  have h := divided_integral_lower (f := C) (a := 4) (b := x-1) (c := cCoef) (R := S-2) 3
    (by norm_num) (by linarith) (by linarith) (by norm_num [cCoef,bCoef,base,S]) C_continuous
    (fun v hv => C_lower hv.1 (by linarith [hv.2]))
  change _ ≤ D x at h
  convert h using 1; dsimp [dCoef]; ring

/-- A small positive fourth recurrence term is retained in the first classical slot. -/
theorem E_lower : (21:ℝ)/10000000 ≤ E (1327/200) := by
  have h := divided_integral_lower (f := D) (a := 5) (b := S-1) (c := dCoef) (R := S-1) 4
    (by norm_num) (by norm_num [S]) le_rfl (by norm_num [dCoef,cCoef,bCoef,base,S]) D_continuous
    (fun v hv => D_lower hv.1 hv.2)
  change _ ≤ E S at h
  apply le_trans _ h
  norm_num [dCoef,cCoef,bCoef,base,S]

end WuPaper.ClassicalE
#print axioms WuPaper.ClassicalE.E_lower
