import MathlibNt.Wu2008DoubleSieve.FourSeventhsBuchstab

namespace WuSource.SrcBuchstab

open Set Real MeasureTheory LiLiuPrereqBuchstab

def poly (c : Fin 7 → ℝ) (x : ℝ) : ℝ :=
  c 0 + c 1 * x + c 2 * x ^ 2 + c 3 * x ^ 3 +
    c 4 * x ^ 4 + c 5 * x ^ 5 + c 6 * x ^ 6

def slope (c : Fin 7 → ℝ) (x : ℝ) : ℝ :=
  c 1 + 2 * c 2 * x + 3 * c 3 * x ^ 2 +
    4 * c 4 * x ^ 3 + 5 * c 5 * x ^ 4 + 6 * c 6 * x ^ 5

def weightedCoeffs (a : ℝ) (c : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![c 0 + a * c 1, 2 * (c 1 + a * c 2), 3 * (c 2 + a * c 3),
    4 * (c 3 + a * c 4), 5 * (c 4 + a * c 5),
    6 * (c 5 + a * c 6), 7 * c 6]

theorem hasDerivAt_poly (c : Fin 7 → ℝ) (x : ℝ) :
    HasDerivAt (poly c) (slope c x) x := by
  convert ((((((hasDerivAt_const x (c 0)).add
    ((hasDerivAt_id x).const_mul (c 1))).add
    (((hasDerivAt_id x).pow 2).const_mul (c 2))).add
    (((hasDerivAt_id x).pow 3).const_mul (c 3))).add
    (((hasDerivAt_id x).pow 4).const_mul (c 4))).add
    (((hasDerivAt_id x).pow 5).const_mul (c 5))).add
    (((hasDerivAt_id x).pow 6).const_mul (c 6)) using 1 <;>
    simp [poly, slope] <;> ring

theorem weighted_derivative (a : ℝ) (c : Fin 7 → ℝ) (x : ℝ) :
    HasDerivAt (fun z => (a + z) * poly c z)
      (poly (weightedCoeffs a c) x) x := by
  convert ((hasDerivAt_id x).const_add a).mul (hasDerivAt_poly c x) using 1
  simp [poly, slope, weightedCoeffs]
  ring

def deficit (c : Fin 7 → ℝ) (h : ℝ) : ℝ :=
  max (-(c 1)) 0 * h + max (-(c 2)) 0 * h ^ 2 +
    max (-(c 3)) 0 * h ^ 3 + max (-(c 4)) 0 * h ^ 4 +
    max (-(c 5)) 0 * h ^ 5 + max (-(c 6)) 0 * h ^ 6

theorem term_lower {c x h : ℝ} (hx : 0 ≤ x) (hxh : x ≤ h) (n : ℕ) :
    -(max (-c) 0 * h ^ n) ≤ c * x ^ n := by
  have hp := pow_le_pow_left₀ hx hxh n
  have hpx : 0 ≤ x ^ n := pow_nonneg hx n
  have hc : -max (-c) 0 ≤ c := by have := le_max_left (-c) 0; linarith
  have hm : 0 ≤ max (-c) 0 := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_right hc hpx,
    mul_le_mul_of_nonneg_left hp hm]

theorem poly_nonneg {c : Fin 7 → ℝ} {x h : ℝ}
    (hx : 0 ≤ x) (hxh : x ≤ h) (hc : deficit c h ≤ c 0) :
    0 ≤ poly c x := by
  have h1 := term_lower (c := c 1) hx hxh 1
  have h2 := term_lower (c := c 2) hx hxh 2
  have h3 := term_lower (c := c 3) hx hxh 3
  have h4 := term_lower (c := c 4) hx hxh 4
  have h5 := term_lower (c := c 5) hx hxh 5
  have h6 := term_lower (c := c 6) hx hxh 6
  simp only [pow_one] at h1
  dsimp [poly, deficit] at *
  linarith

def bernstein (c : Fin 7 → ℝ) (h : ℝ) : Fin 7 → ℝ :=
  ![c 0,
    c 0 + c 1 * h / 6,
    c 0 + c 1 * h / 3 + c 2 * h ^ 2 / 15,
    c 0 + c 1 * h / 2 + c 2 * h ^ 2 / 5 + c 3 * h ^ 3 / 20,
    c 0 + 2 * c 1 * h / 3 + 2 * c 2 * h ^ 2 / 5 +
      c 3 * h ^ 3 / 5 + c 4 * h ^ 4 / 15,
    c 0 + 5 * c 1 * h / 6 + 2 * c 2 * h ^ 2 / 3 +
      c 3 * h ^ 3 / 2 + c 4 * h ^ 4 / 3 + c 5 * h ^ 5 / 6,
    poly c h]

theorem bernstein_cap {c : Fin 7 → ℝ} {h x b : ℝ} (hh : 0 < h)
    (hx : 0 ≤ x) (hxh : x ≤ h)
    (hc : ∀ i : Fin 7, bernstein c h i ≤ b) : poly c x ≤ b := by
  let z := x / h
  have hz : 0 ≤ z := div_nonneg hx hh.le
  have hz' : 0 ≤ 1 - z := by
    dsimp [z]
    have := (div_le_one hh).2 hxh
    linarith
  have he : b - poly c (h * z) =
      (b - bernstein c h 0) * (1 - z) ^ 6 +
      6 * (b - bernstein c h 1) * z * (1 - z) ^ 5 +
      15 * (b - bernstein c h 2) * z ^ 2 * (1 - z) ^ 4 +
      20 * (b - bernstein c h 3) * z ^ 3 * (1 - z) ^ 3 +
      15 * (b - bernstein c h 4) * z ^ 4 * (1 - z) ^ 2 +
      6 * (b - bernstein c h 5) * z ^ 5 * (1 - z) +
      (b - bernstein c h 6) * z ^ 6 := by
    simp [bernstein, poly]
    ring
  have h0 := sub_nonneg.mpr (hc 0)
  have h1 := sub_nonneg.mpr (hc 1)
  have h2 := sub_nonneg.mpr (hc 2)
  have h3 := sub_nonneg.mpr (hc 3)
  have h4 := sub_nonneg.mpr (hc 4)
  have h5 := sub_nonneg.mpr (hc 5)
  have h6 := sub_nonneg.mpr (hc 6)
  have hb : 0 ≤ b - poly c (h * z) := by rw [he]; positivity
  have hzx : h * z = x := by dsimp [z]; field_simp
  rw [hzx] at hb
  linarith

#check monotoneOn_of_hasDerivWithinAt_nonneg
#check monotoneOn_of_deriv_nonneg

end WuSource.SrcBuchstab
