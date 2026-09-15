import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureBuchstab

/-! Factorial contraction for the actual Buchstab slope. The tail bound is
produced from the installed delay equation, not supplied as a hypothesis. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Real LiLiuPrereqBuchstab

/-- The literal delay quotient equals the derivative on the regular tail. -/
theorem slope_formula {u : ℝ} (hu : 2 < u) :
    buchstabSlope u = (buchstab (u - 1) - buchstab u) / u := by
  simp only [buchstabSlope, not_le.mpr hu, if_false]

/-- A one-step estimate for an entire half-line, not merely a single interval. -/
theorem slope_tail_step {M C : ℝ} (hM : 3 ≤ M) (hC : 0 ≤ C)
    (h : ∀ u : ℝ, M ≤ u → |buchstabSlope u| ≤ C) :
    ∀ u : ℝ, M + 1 ≤ u → |buchstabSlope u| ≤ C / (M + 1) := by
  intro u hu
  have hdiff : |buchstab u - buchstab (u - 1)| ≤ C := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := buchstab) (f' := buchstabSlope) (s := Ici M) (C := C)
      (fun x hx => (hasDerivAt_buchstab_off_two (by
        change M ≤ x at hx
        linarith) (by
        change M ≤ x at hx
        linarith)).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using h x hx)
      (convex_Ici M) (show u - 1 ∈ Ici M by change M ≤ u - 1; linarith)
      (show u ∈ Ici M by change M ≤ u; linarith)
    simpa only [Real.norm_eq_abs, show u - (u - 1) = 1 by ring, abs_one, mul_one] using hh
  rw [slope_formula (by linarith), abs_div, abs_of_pos (by linarith : 0 < u),
    abs_sub_comm]
  exact (div_le_div_of_nonneg_right hdiff (by linarith)).trans
    (div_le_div_of_nonneg_left hC (by linarith) hu)

/-- The first regular half-line already gains the factor 1/3. -/
theorem slope_tail_three {u : ℝ} (hu : 3 ≤ u) : |buchstabSlope u| ≤ 1 / 3 := by
  have hdiff := primeOrdered_buchstab_lipschitz
    (u := u - 1) (v := u) (by linarith) (by linarith)
  have hd : |buchstab (u - 1) - buchstab u| ≤ 1 := by
    simpa only [show u - 1 - u = -1 by ring, abs_neg, abs_one] using hdiff
  rw [slope_formula (by linarith), abs_div, abs_of_pos (by linarith : 0 < u)]
  exact (div_le_div_of_nonneg_right hd (by linarith)).trans
    (one_div_le_one_div_of_le (by norm_num) hu)

/-- Uniform factorial decay, with the natural threshold quantified before u. -/
theorem slope_factorial (k : ℕ) :
    ∀ u : ℝ, (k : ℝ) + 3 ≤ u →
      |buchstabSlope u| ≤ 2 / (((k + 3).factorial : ℕ) : ℝ) := by
  induction k with
  | zero =>
    intro u hu
    have hu' : 3 ≤ u := by simpa using hu
    convert slope_tail_three hu' using 1
    norm_num [Nat.factorial_succ]
  | succ k ih =>
    intro u hu
    have hc : 0 ≤ (2 : ℝ) / ((k + 3).factorial : ℝ) := by positivity
    have hstep := slope_tail_step (M := (k : ℝ) + 3) (by
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith) hc ih u (by
        push_cast at hu
        linarith)
    have he : (2 / ((k + 3).factorial : ℝ)) / ((k : ℝ) + 3 + 1) =
        2 / ((k + 1 + 3).factorial : ℝ) := by
      have hf : (((k + 3 + 1).factorial : ℕ) : ℝ) =
          ((k : ℝ) + 3 + 1) * ((k + 3).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_succ (k + 3)
      rw [show k + 1 + 3 = k + 3 + 1 by omega, hf, div_div]
      congr 1
      ring
    rw [he] at hstep
    exact hstep

/-- The factorial slope controls actual Buchstab increments anywhere on the tail. -/
theorem buchstab_tail_increment (k : ℕ) {x y : ℝ}
    (hx : (k : ℝ) + 3 ≤ x) (hy : (k : ℝ) + 3 ≤ y) :
    |buchstab y - buchstab x| ≤
      (2 / ((k + 3).factorial : ℝ)) * |y - x| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := buchstab) (f' := buchstabSlope) (s := Ici ((k : ℝ) + 3))
    (C := 2 / ((k + 3).factorial : ℝ))
    (fun u hu => (hasDerivAt_buchstab_off_two (by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      change (k : ℝ) + 3 ≤ u at hu
      linarith) (by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      change (k : ℝ) + 3 ≤ u at hu
      linarith)).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using slope_factorial k u hu)
    (convex_Ici _) hx hy
  simpa only [Real.norm_eq_abs] using hh

end Wu2008DoubleSieve.SecondFunctionalJointTail
