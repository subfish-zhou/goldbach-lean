import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryPoissonTail

/-!
# An actual W phase: CRT peeling and reciprocal inversion

This is the first reciprocal step of Fouvry (1984), p. 238, (8.14), applied
to the existing product CRT residue. The moduli `q,r` need not be coprime.
The peeled factor `k` is coprime to its complement in their lcm. No five-gcd
decomposition, small-modulus bound, or estimate for the finite remainder is
asserted here. In particular the complementary phase has not been discarded.
-/

noncomputable section

open scoped FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Signed Bezout representative of the inverse of `n` modulo `m`. -/
def wPhaseInverse (n m : ℕ) : ℤ := n.gcdA m

theorem wPhaseInverse_spec {n m : ℕ} (h : n.Coprime m) :
    Int.ModEq m ((n : ℤ) * wPhaseInverse n m) 1 := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨n.gcdB m, ?_⟩
  have hb := Nat.gcd_eq_gcd_ab n m
  rw [h.gcd_eq_one, Nat.cast_one] at hb
  dsimp [wPhaseInverse]
  linarith

/-- Integer congruences give equal normalized phases, also for modulus one. -/
theorem wPhase_circle_eq_of_modEq {m : ℕ} (hm : 0 < m) {x y : ℤ}
    (h : Int.ModEq m x y) :
    (((x : ℝ) / m : ℝ) : UnitAddCircle) = ((y : ℝ) / m : ℝ) := by
  obtain ⟨z, hz⟩ := h.dvd
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-z, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hz' : (y : ℝ) - x = m * (z : ℝ) := by exact_mod_cast hz
  simp only [zsmul_eq_mul, Int.cast_neg, mul_one]
  field_simp
  nlinarith


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
