import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerRoots

/-!
Elementary quadratic Gauss cancellation by translation and additive orthogonality.
The linear coefficient is unrestricted; no multiplicative character is used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_quadratic_gauss_norm (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (A B : ZMod p) (hA : A ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (A * x ^ 2 + B * x)‖ = Real.sqrt (p : ℝ) := by
  classical
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  let S := ∑ x : ZMod p, ψ (A * x ^ 2 + B * x)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim (Fact.out : p.Prime).ne_one hp2
  have hs : S * starRingEnd ℂ S = (p : ℂ) := by
    calc
      _ = ∑ x : ZMod p, ∑ y : ZMod p,
          ψ (A * x ^ 2 + B * x - (A * y ^ 2 + B * y)) := by
        simp only [S, map_sum, sum_mul, mul_sum, sub_eq_add_neg,
          AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
        exact sum_comm
      _ = ∑ y : ZMod p, ∑ x : ZMod p,
          ψ (A * (x + y) ^ 2 + B * (x + y) - (A * y ^ 2 + B * y)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        exact (Equiv.sum_comp (Equiv.addRight y)
          (fun x ↦ ψ (A * x ^ 2 + B * x - (A * y ^ 2 + B * y)))).symm
      _ = ∑ x : ZMod p, ψ (A * x ^ 2 + B * x) *
          ∑ y : ZMod p, ψ ((2 * A * x) * y) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [mul_sum]
        apply sum_congr rfl
        intro y _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = (p : ℂ) := by
        rw [sum_eq_single 0]
        · simp only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero,
            AddChar.map_zero_eq_one, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
            mul_one, one_mul]
        · intro x _ hx
          have hzero : ∑ y : ZMod p, ψ ((2 * A * x) * y) = 0 :=
            AddChar.sum_eq_zero_of_ne_one
              (ZMod.isPrimitive_stdAddChar p (mul_ne_zero (mul_ne_zero htwo hA) hx))
          rw [hzero, mul_zero]
        · simp
  have hsq : ‖S‖ ^ 2 = (p : ℝ) := by
    have he := (Complex.mul_conj S).symm.trans hs
    rw [Complex.normSq_eq_norm_sq] at he
    exact_mod_cast he
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  exact hsq

theorem oddPrimePower_sum_reduction (q r : ℕ) [NeZero q] [NeZero r]
    (F : ZMod q → ℂ) :
    (∑ x : ZMod (q * r), F (ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) x)) =
      (r : ℂ) * ∑ y : ZMod q, F y := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  calc
    _ = ∑ y : ZMod q, ∑ x ∈ univ.filter (fun x ↦ f x = y), F (f x) :=
      (sum_fiberwise univ f (fun x ↦ F (f x))).symm
    _ = ∑ y : ZMod q, (r : ℂ) * F y := by
      apply sum_congr rfl
      intro y _
      rw [sum_congr rfl (fun x hx ↦ congrArg F (mem_filter.mp hx).2)]
      simp only [sum_const, nsmul_eq_mul, f, zmod_reduction_fiber_card]
    _ = _ := (mul_sum _ _ _).symm

private theorem oddPrimePower_shifted_inverse_product {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 3 = 0) :
    (u + t) * (u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3) = 1 := by
  have hi := ZMod.mul_inv_of_unit u hu
  linear_combination (1 - t * u⁻¹ + t ^ 2 * (u⁻¹) ^ 2) * hi + (u⁻¹) ^ 3 * ht

theorem oddPrimePower_isUnit_add_cube_zero {q : ℕ} (u t : ZMod q)
    (ht : t ^ 3 = 0) : IsUnit (u + t) ↔ IsUnit u := by
  have step (v s : ZMod q) (hv : IsUnit v) (hs : s ^ 3 = 0) : IsUnit (v + s) :=
    isUnit_iff_exists_inv.mpr ⟨_, oddPrimePower_shifted_inverse_product v s hv hs⟩
  constructor
  · intro hu
    simpa only [add_neg_cancel_right] using step (u + t) (-t) hu (by
      rw [neg_pow, ht, mul_zero])
  · exact fun hu ↦ step u t hu ht

theorem oddPrimePower_inv_add_cube_zero {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 3 = 0) :
    (u + t)⁻¹ = u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3 := by
  have hs := oddPrimePower_shifted_inverse_product u t hu ht
  have hi := ZMod.inv_mul_of_unit (u + t)
    ((oddPrimePower_isUnit_add_cube_zero u t ht).mpr hu)
  calc
    _ = (u + t)⁻¹ * ((u + t) * (u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3)) := by
      rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
