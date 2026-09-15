import E09JointMainMajorLog

noncomputable section
open Real Set Wu2008DoubleSieve

namespace WuTarget.E09JointMainMajor

theorem log_three_upper : log (3 : ℝ) ≤ 109862 / 100000 := by
  have h1 := log_upper (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have h2 := log_upper (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have he := W11Credit.log_three_identity
  norm_num [upperLog, lowerLog] at h1 h2
  linarith only [h1, h2, he]

theorem log_tangent_quadratic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    log (3 - x) ≤ log 3 - x / 3 - x ^ 2 / 18 := by
  let F : ℝ → ℝ := fun x => log 3 - x / 3 - x ^ 2 / 18 - log (3 - x)
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt F (x ^ 2 / (9 * (3 - x))) x := by
    have hn : 3 - x ≠ 0 := by linarith [hx.2]
    convert! (((hasDerivAt_const x (log (3 : ℝ))).sub
      ((hasDerivAt_id x).div_const 3)).sub (((hasDerivAt_id x).pow 2).div_const 18)).sub
      (((hasDerivAt_const x (3 : ℝ)).sub (hasDerivAt_id x)).log hn) using 1
    dsimp
    field_simp [hn]
    ring
  have hm : MonotoneOn F (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hh := interior_subset hx
      rw [(hd x hh).deriv]
      exact div_nonneg (sq_nonneg x) (by linarith [hh.2])
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ⟨hx, hx1⟩ hx
  have hz : F 0 = 0 := by norm_num [F]
  rw [hz] at h
  dsimp [F] at h
  linarith only [h]

def curvaturePolynomial (x : ℝ) : ℝ :=
  (7 / 30 + (4 / 9) * x + (5 / 54) * x ^ 2) *
    (1 / 16 + x / 32 + 3 * x ^ 2 / 256)

theorem variable_curvature {v : ℝ} (hv : v ∈ Icc (4 : ℝ) 5) :
    curvaturePolynomial (5 - v) ≤
      (1 + 1 / (v - 2) - log (v - 2)) / (v - 1) ^ 2 := by
  let x := 5 - v
  have hx : 0 ≤ x := by dsimp [x]; linarith [hv.2]
  have hx1 : x ≤ 1 := by dsimp [x]; linarith [hv.1]
  have hn : 0 < 3 - x := by linarith
  have hd : 0 < 4 - x := by linarith
  have hr : 1 / 3 + x / 9 + x ^ 2 / 27 ≤ 1 / (3 - x) := by
    apply (le_div_iff₀ hn).2
    nlinarith only [pow_nonneg hx 3]
  have hl := log_tangent_quadratic hx hx1
  have hnum : 7 / 30 + (4 / 9) * x + (5 / 54) * x ^ 2 ≤
      1 + 1 / (3 - x) - log (3 - x) := by
    linarith only [hr, hl, log_three_upper]
  have hrec : 1 / 16 + x / 32 + 3 * x ^ 2 / 256 ≤ 1 / (4 - x) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd)).2
    have hp := mul_nonneg (pow_nonneg hx 3) (show 0 ≤ 16 - 3 * x by linarith)
    nlinarith only [hp]
  have hpoly : 0 ≤ 7 / 30 + (4 / 9) * x + (5 / 54) * x ^ 2 := by positivity
  have hm := mul_le_mul hnum hrec (by positivity) (hpoly.trans hnum)
  have he2 : v - 2 = 3 - x := by dsimp [x]; ring
  have he1 : v - 1 = 4 - x := by dsimp [x]; ring
  rw [he2, he1]
  unfold curvaturePolynomial
  dsimp only [x] at hm
  convert! hm using 1 <;> ring

def curvaturePrimitive (x : ℝ) : ℝ :=
  (7 / 480) * x ^ 2 / 2 +
    (7 / 960 + 1 / 36) * x ^ 3 / 6 +
    (7 / 2560 + 1 / 72 + 5 / 864) * x ^ 4 / 12 +
    (1 / 192 + 5 / 1728) * x ^ 5 / 20 +
    (5 / 4608) * x ^ 6 / 30

def curvatureSlope (x : ℝ) : ℝ :=
  (7 / 480) * x +
    (7 / 960 + 1 / 36) * x ^ 2 / 2 +
    (7 / 2560 + 1 / 72 + 5 / 864) * x ^ 3 / 3 +
    (1 / 192 + 5 / 1728) * x ^ 4 / 4 +
    (5 / 4608) * x ^ 5 / 5

theorem curvaturePrimitive_derivative (x : ℝ) :
    HasDerivAt curvaturePrimitive (curvatureSlope x) x := by
  unfold curvaturePrimitive
  convert! ((((((hasDerivAt_id x).pow 2).const_mul (7 / 480)).div_const 2).add
    ((((hasDerivAt_id x).pow 3).const_mul (7 / 960 + 1 / 36)).div_const 6)).add
    ((((hasDerivAt_id x).pow 4).const_mul (7 / 2560 + 1 / 72 + 5 / 864)).div_const 12)).add
    ((((hasDerivAt_id x).pow 5).const_mul (1 / 192 + 5 / 1728)).div_const 20) |>.add
    ((((hasDerivAt_id x).pow 6).const_mul (5 / 4608)).div_const 30) using 1
  dsimp [curvatureSlope]
  ring

theorem curvatureSlope_derivative (x : ℝ) :
    HasDerivAt curvatureSlope (curvaturePolynomial x) x := by
  unfold curvatureSlope
  convert! (((((hasDerivAt_id x).const_mul (7 / 480)).add
    ((((hasDerivAt_id x).pow 2).const_mul (7 / 960 + 1 / 36)).div_const 2)).add
    ((((hasDerivAt_id x).pow 3).const_mul (7 / 2560 + 1 / 72 + 5 / 864)).div_const 3)).add
    ((((hasDerivAt_id x).pow 4).const_mul (1 / 192 + 5 / 1728)).div_const 4)).add
    ((((hasDerivAt_id x).pow 5).const_mul (5 / 4608)).div_const 5) using 1
  dsimp [curvaturePolynomial]
  ring

def correctedUpper (v : ℝ) : ℝ := wuUpperCoefficient v - curvaturePrimitive (5 - v)

def correctedDensity (v : ℝ) : ℝ := GConvexChord.density v + curvatureSlope (5 - v)

theorem correctedUpper_derivative {v : ℝ} (hv : v ∈ Icc (4 : ℝ) 5) :
    HasDerivAt correctedUpper (correctedDensity v) v := by
  convert! (GConvexChord.upper_derivative hv).sub
    ((curvaturePrimitive_derivative (5 - v)).comp v
      ((hasDerivAt_const v (5 : ℝ)).sub (hasDerivAt_id v))) using 1
  dsimp [correctedDensity]
  ring

theorem correctedDensity_derivative {v : ℝ} (hv : v ∈ Icc (4 : ℝ) 5) :
    HasDerivAt correctedDensity
      ((1 + 1 / (v - 2) - log (v - 2)) / (v - 1) ^ 2 - curvaturePolynomial (5 - v)) v := by
  convert! (GConvexChord.density_derivative hv).add
    ((curvatureSlope_derivative (5 - v)).comp v
      ((hasDerivAt_const v (5 : ℝ)).sub (hasDerivAt_id v))) using 1
  ring

theorem correctedDensity_monotone : MonotoneOn correctedDensity (Icc (4 : ℝ) 5) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro v hv; exact (correctedDensity_derivative hv).continuousAt.continuousWithinAt
  · intro v hv
    exact (correctedDensity_derivative (interior_subset hv)).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [(correctedDensity_derivative (interior_subset hv)).deriv]
    exact sub_nonneg.mpr (variable_curvature (interior_subset hv))

theorem correctedUpper_convex : ConvexOn ℝ (Icc (4 : ℝ) 5) correctedUpper := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · intro v hv; exact (correctedUpper_derivative hv).continuousAt.continuousWithinAt
  · intro v hv
    exact (correctedUpper_derivative (interior_subset hv)).differentiableAt.differentiableWithinAt
  · intro v hv w hw hvw
    rw [(correctedUpper_derivative (interior_subset hv)).deriv,
      (correctedUpper_derivative (interior_subset hw)).deriv]
    exact correctedDensity_monotone (interior_subset hv) (interior_subset hw) hvw

def chordDefect (v : ℝ) : ℝ :=
  (5 - v) * curvaturePrimitive 1 - curvaturePrimitive (5 - v)

theorem variable_chord_defect {v : ℝ} (hv : v ∈ Icc (4 : ℝ) 5) :
    chordDefect v ≤
      (5 - v) * wuUpperCoefficient 4 + (v - 4) * wuUpperCoefficient 5 -
        wuUpperCoefficient v := by
  have h := correctedUpper_convex.2
    (by norm_num : (4 : ℝ) ∈ Icc (4 : ℝ) 5)
    (by norm_num : (5 : ℝ) ∈ Icc (4 : ℝ) 5)
    (show 0 ≤ 5 - v by linarith [hv.2]) (show 0 ≤ v - 4 by linarith [hv.1])
    (show (5 - v) + (v - 4) = 1 by ring)
  simp only [smul_eq_mul, show (5 - v) * 4 + (v - 4) * 5 = v by ring] at h
  unfold correctedUpper at h
  norm_num [curvaturePrimitive] at h
  unfold chordDefect curvaturePrimitive
  linarith only [h]

end WuTarget.E09JointMainMajor
