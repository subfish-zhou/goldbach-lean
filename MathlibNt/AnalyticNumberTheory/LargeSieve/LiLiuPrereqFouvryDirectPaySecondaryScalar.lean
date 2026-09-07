import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryWeight

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Both section-length contributions are paid after the original reciprocal.
The second summand is never bounded by the first local summand. -/
theorem directPaySecondary_scalar
    {D d k n r s H Z x T R S m E : ℝ}
    (hD : 1 ≤ D) (hd : 0 ≤ d) (hdZ : d ≤ Z ^ 5)
    (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hZ : 1 ≤ Z) (hx : 0 < x) (hT : 1 ≤ T) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hm : 0 ≤ m) (hE : 0 ≤ E)
    (hkRS : k ≤ R * S) (hnT : n ≤ 2 * T) (hrR : r ≤ R) (hsS : s ≤ S)
    (hH : H ≤ 32 * D * k * r * s * Z * T / x) :
    ((D * k * r * s)⁻¹) ^ 2 * (m * (8 * k * r * T)) *
      (E * H * n ^ 2 * T ^ 2 * r * Real.sqrt r * s ^ 3 *
        (d + 2 * k / (n * r * s * s))) / T ^ 4 ≤
      2048 * E * m * Z ^ 6 * T ^ 2 * R * Real.sqrt R * S ^ 3 / x := by
  have hD0 : 0 < D := by linarith
  have hT0 : 0 < T := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hZ5 : 1 ≤ Z ^ 5 := one_le_pow₀ hZ
  have hn2 : n ^ 2 ≤ 4 * T ^ 2 := by nlinarith [sq_nonneg (2 * T - n)]
  have hs2 : s ^ 2 ≤ S ^ 3 := by
    calc
      _ ≤ S ^ 2 := by gcongr
      _ ≤ S ^ 2 * S := le_mul_of_one_le_right (sq_nonneg S) hS
      _ = _ := by ring
  have hSS : S ≤ S ^ 3 := by nlinarith [sq_nonneg (S - 1)]
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hb1 : n ^ 2 * r * Real.sqrt r * s ^ 2 * d ≤
      4 * T ^ 2 * R * Real.sqrt R * S ^ 3 * Z ^ 5 := by gcongr
  have hb2 : 2 * k * n * Real.sqrt r ≤
      4 * T ^ 2 * R * Real.sqrt R * S ^ 3 * Z ^ 5 := by
    calc
      _ ≤ 2 * (R * S) * (2 * T) * Real.sqrt R := by gcongr
      _ = 4 * T * R * Real.sqrt R * S := by ring
      _ ≤ 4 * T ^ 2 * R * Real.sqrt R * S ^ 3 := by gcongr
      _ ≤ (4 * T ^ 2 * R * Real.sqrt R * S ^ 3) * Z ^ 5 :=
        le_mul_of_one_le_right (by positivity) hZ5
  have hb : n ^ 2 * r * Real.sqrt r * s ^ 2 * d + 2 * k * n * Real.sqrt r ≤
      8 * T ^ 2 * R * Real.sqrt R * S ^ 3 * Z ^ 5 := by linarith
  calc
    _ ≤ ((D * k * r * s)⁻¹) ^ 2 * (m * (8 * k * r * T)) *
      (E * (32 * D * k * r * s * Z * T / x) * n ^ 2 * T ^ 2 * r *
        Real.sqrt r * s ^ 3 * (d + 2 * k / (n * r * s * s))) / T ^ 4 := by gcongr
    _ = (256 * E * m * Z / (x * D)) *
        (n ^ 2 * r * Real.sqrt r * s ^ 2 * d + 2 * k * n * Real.sqrt r) := by
      field_simp
      ring
    _ ≤ (256 * E * m * Z / x) *
        (8 * T ^ 2 * R * Real.sqrt R * S ^ 3 * Z ^ 5) := by
      apply mul_le_mul _ hb (by positivity) (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) hx
      exact le_mul_of_one_le_right hx.le hD
    _ = _ := by ring

/-- Root extraction is monotone even if the original energy is totalized below zero. -/
theorem directPaySecondary_root_of_sq {A mass energy U T B : ℝ}
    (hA : 0 ≤ A) (hm : 0 ≤ mass) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (he : energy ≤ U) (hb : A ^ 2 * mass * U / T ^ 4 ≤ B ^ 2) :
    A * Real.sqrt mass * Real.sqrt energy / T ^ 2 ≤ B := by
  have he' : A * Real.sqrt mass * Real.sqrt energy / T ^ 2 ≤
      A * Real.sqrt mass * Real.sqrt U / T ^ 2 := by gcongr
  apply he'.trans
  apply (sq_le_sq₀ (by positivity) hB).mp
  calc
    _ = A ^ 2 * mass * U / T ^ 4 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hm, Real.sq_sqrt hU]
      ring
    _ ≤ _ := hb

/-- Exact square of the requested secondary body. -/
theorem directPaySecondary_body_sq {x R S T : ℝ}
    (hx : 0 ≤ x) (hR : 0 < R) (hS : 0 ≤ S) :
    (T * R ^ (3 / 4 : ℝ) * S ^ (3 / 2 : ℝ) / Real.sqrt x) ^ 2 =
      T ^ 2 * R * Real.sqrt R * S ^ 3 / x := by
  have hr : (R ^ (3 / 4 : ℝ)) ^ 2 = R * Real.sqrt R := by
    rw [← Real.rpow_natCast (R ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hR.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hs : (S ^ (3 / 2 : ℝ)) ^ 2 = S ^ 3 := by
    rw [← Real.rpow_natCast (S ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hS]
    norm_num
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hx, hr, hs]
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
