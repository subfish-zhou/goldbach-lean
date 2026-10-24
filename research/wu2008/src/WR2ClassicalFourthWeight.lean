import WR2ClassicalQuotient

noncomputable section
namespace WuPaper.ClassicalFourth
open Real Set

def R : ℝ := 1327/200
def weight (s : ℝ) : ℝ := 2*(1/s+1/(R-s))
def weightD1 (s : ℝ) : ℝ := 2*(-1/s^2+1/(R-s)^2)
def weightD2 (s : ℝ) : ℝ := 4*(1/s^3+1/(R-s)^3)

theorem weight_deriv {s : ℝ} (hs : s ≠ 0) (hr : R-s ≠ 0) :
    HasDerivAt weight (weightD1 s) s := by
  have h := (((hasDerivAt_const s (1:ℝ)).div (hasDerivAt_id s) hs).add
    ((hasDerivAt_const s (1:ℝ)).div ((hasDerivAt_const s R).sub (hasDerivAt_id s)) hr)).const_mul 2
  change HasDerivAt weight _ s at h
  apply h.congr_deriv
  dsimp [weightD1]
  ring

theorem weightD1_deriv {s : ℝ} (hs : s ≠ 0) (hr : R-s ≠ 0) :
    HasDerivAt weightD1 (weightD2 s) s := by
  have h := (((hasDerivAt_const s (-1:ℝ)).div ((hasDerivAt_id s).pow 2) (pow_ne_zero 2 hs)).add
    ((hasDerivAt_const s (1:ℝ)).div (((hasDerivAt_const s R).sub (hasDerivAt_id s)).pow 2)
      (pow_ne_zero 2 hr))).const_mul 2
  change HasDerivAt weightD1 _ s at h
  apply h.congr_deriv
  dsimp [weightD2]
  field_simp
  ring

theorem weight_literal {s : ℝ} (hs : s ≠ 0) (hr : R-s ≠ 0) :
    weight s = 1/(s*((1:ℝ)/2-(100/1327)*s)) := by
  have he : (1:ℝ)/2-(100/1327)*s = (100/1327)*(R-s) := by
    unfold R
    ring
  rw [he]
  unfold weight
  field_simp [hs,hr]
  norm_num [R]

theorem weight_bounds {s : ℝ} (hs : 3 ≤ s) (hr : s ≤ R-1) :
    |weight s| ≤ (8:ℝ)/3 ∧ |weightD1 s| ≤ (20:ℝ)/9 ∧ |weightD2 s| ≤ (112:ℝ)/27 := by
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < R-s := by linarith
  have ha0 : 0 ≤ s⁻¹ := (inv_pos.mpr hs0).le
  have hb0 : 0 ≤ (R-s)⁻¹ := (inv_pos.mpr hr0).le
  have ha : s⁻¹ ≤ (1:ℝ)/3 := by rw [← one_div]; apply (div_le_iff₀ hs0).mpr; linarith
  have hb : (R-s)⁻¹ ≤ 1 := by rw [← one_div]; apply (div_le_iff₀ hr0).mpr; linarith
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  have hb2 := pow_le_pow_left₀ hb0 hb 2
  have ha3 := pow_le_pow_left₀ ha0 ha 3
  have hb3 := pow_le_pow_left₀ hb0 hb 3
  have hw : weight s = 2*(s⁻¹+(R-s)⁻¹) := by simp [weight,one_div]
  have hw1 : weightD1 s = 2*(-(s⁻¹)^2+((R-s)⁻¹)^2) := by simp [weightD1,div_eq_mul_inv,inv_pow]
  have hw2 : weightD2 s = 4*((s⁻¹)^3+((R-s)⁻¹)^3) := by simp [weightD2,one_div,inv_pow]
  constructor
  · rw [hw,abs_of_nonneg (by positivity)]
    linarith only [ha,hb]
  constructor
  · rw [hw1]
    apply abs_le.mpr
    constructor <;> nlinarith only [ha2,hb2,sq_nonneg (s⁻¹),sq_nonneg ((R-s)⁻¹)]
  · rw [hw2,abs_of_nonneg (by positivity)]
    linarith only [ha3,hb3]

end WuPaper.ClassicalFourth
#print axioms WuPaper.ClassicalFourth.weightD1_deriv
#print axioms WuPaper.ClassicalFourth.weight_bounds
