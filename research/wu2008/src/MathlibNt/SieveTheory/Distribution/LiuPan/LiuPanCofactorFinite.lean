import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

/-!
Pan--Wang--Ding (1975), original p.601, (2.6): finite cofactor transport.
The payload is arbitrary; in the application it is the whole-a norm, not
an a-wise triangle majorant. All positive divisors, including d=1, are retained.
-/
namespace AnalyticNumberTheory.LargeSieve.PanCofactor
open Finset
open scoped BigOperators

/-- Exact cofactor bijection `(q,d) ↦ (q/d,d)`, inverse `(m,d) ↦ (m*d,d)`.
No positivity is required of the real payload in this equality. -/
theorem sum_divisors_eq_hyperbola (G : ℕ → ℕ → ℝ) (D : ℕ) :
    (∑ q ∈ Icc 1 D, ∑ d ∈ q.divisors, G (q / d) d) =
      ∑ m ∈ Icc 1 D, ∑ d ∈ Icc 1 (D / m), G m d := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.1 / x.2, x.2⟩)
    (fun x _ => ⟨x.1 * x.2, x.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, d⟩ hx
    obtain ⟨hq, hd⟩ := mem_sigma.mp hx
    obtain ⟨hqpos, hqD⟩ := mem_Icc.mp hq
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hdpos := Nat.pos_of_dvd_of_pos hdvd hqpos
    have hmpos := Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdpos
    refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨hmpos, (Nat.div_le_self q d).trans hqD⟩,
      mem_Icc.mpr ⟨hdpos, ?_⟩⟩
    exact (Nat.le_div_iff_mul_le hmpos).mpr (by
      rw [Nat.mul_div_cancel' hdvd]
      exact hqD)
  · rintro ⟨m, d⟩ hy
    obtain ⟨hm, hd⟩ := mem_sigma.mp hy
    obtain ⟨hmpos, _hmD⟩ := mem_Icc.mp hm
    obtain ⟨hdpos, hdD⟩ := mem_Icc.mp hd
    have hprodpos := Nat.mul_pos hmpos hdpos
    have hprodD : m * d ≤ D := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hdD
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hprodpos, hprodD⟩,
      Nat.mem_divisors.mpr ⟨dvd_mul_left d m, Nat.ne_of_gt hprodpos⟩⟩
  · rintro ⟨q, d⟩ hx
    have hdvd := (Nat.mem_divisors.mp (mem_sigma.mp hx).2).1
    simp only [Nat.div_mul_cancel hdvd]
  · rintro ⟨m, d⟩ hy
    have hdpos := (mem_Icc.mp (mem_sigma.mp hy).2).1
    simp [Nat.ne_of_gt hdpos]
  · intro x _hx
    rfl

/-- Exact reciprocal-totient ledger before paying the weight. -/
theorem weighted_sum_divisors_eq_hyperbola (F : ℕ → ℕ → ℝ) (D : ℕ) :
    (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors, F (q / d) d) =
      ∑ m ∈ Icc 1 D, ∑ d ∈ Icc 1 (D / m),
        ((m * d).totient : ℝ)⁻¹ * F m d := by
  calc
    _ = ∑ q ∈ Icc 1 D, ∑ d ∈ q.divisors,
        (((q / d) * d).totient : ℝ)⁻¹ * F (q / d) d := by
      apply sum_congr rfl
      intro q _hq
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      rw [Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1]
    _ = _ := sum_divisors_eq_hyperbola (fun m d => ((m * d).totient : ℝ)⁻¹ * F m d) D

/-- Totient supermultiplicativity pays the weight; nonnegativity permits
only enlargement of the hyperbola to the positive D-by-D rectangle. -/
theorem weighted_sum_divisors_le_rectangle
    (F : ℕ → ℕ → ℝ) (hF : ∀ m d, 0 ≤ F m d) (D : ℕ) :
    (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors, F (q / d) d) ≤
      ∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹ *
        ∑ d ∈ Icc 1 D, (d.totient : ℝ)⁻¹ * F m d := by
  rw [weighted_sum_divisors_eq_hyperbola]
  apply sum_le_sum
  intro m hm
  calc
    _ ≤ ∑ d ∈ Icc 1 (D / m),
        (m.totient : ℝ)⁻¹ * ((d.totient : ℝ)⁻¹ * F m d) := by
      apply sum_le_sum
      intro d hd
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        (multiple_inv_totient_le_product m d (mem_Icc.mp hm).1
          (mem_Icc.mp hd).1) (hF m d)
    _ ≤ ∑ d ∈ Icc 1 D,
        (m.totient : ℝ)⁻¹ * ((d.totient : ℝ)⁻¹ * F m d) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact Icc_subset_Icc_right (Nat.div_le_self D m)
      · intro d _hd _hnot
        exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hF m d))
    _ = _ := (mul_sum _ _ _).symm

/-- A uniform whole-payload inner bound leaves precisely the cofactor mass.
This finite implication does not assert an analytic bound for the payload. -/
theorem weighted_sum_divisors_le_uniform
    (F : ℕ → ℕ → ℝ) (hF : ∀ m d, 0 ≤ F m d) (D : ℕ) (M : ℝ)
    (hM : ∀ m ∈ Icc 1 D, ∑ d ∈ Icc 1 D, (d.totient : ℝ)⁻¹ * F m d ≤ M) :
    (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors, F (q / d) d) ≤
      M * ∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹ := by
  refine (weighted_sum_divisors_le_rectangle F hF D).trans ?_
  calc
    _ ≤ ∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹ * M := by
      exact sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hM m hm) (by positivity)
    _ = _ := by rw [← sum_mul, mul_comm]

end AnalyticNumberTheory.LargeSieve.PanCofactor