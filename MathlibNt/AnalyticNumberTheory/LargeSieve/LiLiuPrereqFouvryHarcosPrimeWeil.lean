import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosMinpoly
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosPowerSum
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimePower

/-!
# The odd-prime Kloosterman bound

The polynomial character, its quadratic generating series, the finite Euler
identity, the actual extension trace identity, and the Stepanov point bound
are all proved in the imported modules. Cesaro averaging converts the bound
on the total root power sum into individual bounds without losing multiplicity.
-/

noncomputable section

open Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable (p : ℕ) [Fact p.Prime]

theorem harcosReciprocalRoots_norm_le (hp2 : p ≠ 2) (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (m : ZMod p) (hm : m ≠ 0) :
    ‖harcosReciprocalRootPlus (m * a) (m * b)‖ ≤ Real.sqrt (p : ℝ) ∧
      ‖harcosReciprocalRootMinus (m * a) (m * b)‖ ≤ Real.sqrt (p : ℝ) := by
  let s := (univ : Finset (ZMod p)).erase 0 ×ˢ (univ : Finset Bool)
  let z : ZMod p × Bool → ℂ := fun i =>
    if i.2 then harcosReciprocalRootPlus (i.1 * a) (i.1 * b)
      else harcosReciprocalRootMinus (i.1 * a) (i.1 * b)
  have hsum (n : ℕ) (hn : 4 ≤ n) :
      (∑ i ∈ s, z i ^ n) =
        -(∑ k ∈ (univ : Finset (ZMod p)).erase 0,
          harcosExtensionKloosterman p a b k n) := by
    simp only [s, z, sum_product, Fintype.sum_bool, Bool.false_eq_true,
      if_false, if_true]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    rw [harcosExtensionKloosterman_eq_reciprocalRoots p a b k ha
      (mem_erase.mp hk).1 n (by omega), neg_neg]
  have hg : ∀ᶠ n : ℕ in atTop,
      ‖∑ i ∈ s, z i ^ n‖ ≤ (16 * (p : ℝ) + 1) * Real.sqrt (p : ℝ) ^ n := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    rw [hsum n hn, norm_neg]
    exact harcosExtensionKloosterman_total_growth p hp2 a b ha hb n hn
  have hz := harcos_norm_le_of_finset_power_sum_bound s z
    (Real.sqrt_pos.mpr (show (0 : ℝ) < p by
      exact_mod_cast (Fact.out : p.Prime).pos)) hg
  exact ⟨hz (m, true) (by simp [s, hm]), hz (m, false) (by simp [s, hm])⟩

theorem harcosReciprocalRoots_norm_eq (hp2 : p ≠ 2) (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖harcosReciprocalRootPlus a b‖ = Real.sqrt (p : ℝ) ∧
      ‖harcosReciprocalRootMinus a b‖ = Real.sqrt (p : ℝ) := by
  have hle := harcosReciprocalRoots_norm_le p hp2 a b ha hb 1 one_ne_zero
  simp only [one_mul] at hle
  have hprod := congrArg norm (harcosReciprocalRoots_mul_prime a b ha hb)
  rw [norm_mul, Complex.norm_natCast] at hprod
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have hpos : 0 < Real.sqrt (p : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hl := mul_le_mul_of_nonneg_left hle.2
    (norm_nonneg (harcosReciprocalRootPlus a b))
  have hr := mul_le_mul_of_nonneg_right hle.1
    (norm_nonneg (harcosReciprocalRootMinus a b))
  constructor <;> nlinarith [hle.1, hle.2]

/-- Harcos's Theorem 1 for the actual complete sum, with an arbitrary integer
second frequency and no unproved Weil or root-power premise. -/
theorem completeKloosterman_odd_prime_weil (hp2 : p ≠ 2)
    (a : ZMod p) (d : ℤ) (ha : a ≠ 0) (hd : (d : ZMod p) ≠ 0) :
    ‖completeKloosterman p a d‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hs : harcosReciprocalRootPlus a (d : ZMod p) +
      harcosReciprocalRootMinus a (d : ZMod p) = -completeKloosterman p a d := by
    rw [harcosReciprocalRoots_add, harcosCoefficient_one]
  have hn := harcosReciprocalRoots_norm_eq p hp2 a (d : ZMod p) ha hd
  calc
    ‖completeKloosterman p a d‖ =
        ‖harcosReciprocalRootPlus a (d : ZMod p) +
          harcosReciprocalRootMinus a (d : ZMod p)‖ := by rw [hs, norm_neg]
    _ ≤ ‖harcosReciprocalRootPlus a (d : ZMod p)‖ +
        ‖harcosReciprocalRootMinus a (d : ZMod p)‖ := norm_add_le _ _
    _ = _ := by rw [hn.1, hn.2]; ring

/-- The prime-modulus estimate, including `p = 2` and one zero frequency.
Both frequencies may be arbitrary signed integers; only their simultaneous
vanishing modulo the prime is excluded. -/
theorem completeKloosterman_prime_primitive_weil (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman p (a : ZMod p) d‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hone : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  by_cases hp2 : p = 2
  · subst p
    rw [completeKloosterman_eq_sum_units]
    calc
      _ ≤ ∑ u : (ZMod 2)ˣ, ‖ZMod.stdAddChar
        ((a : ZMod 2) * (u : ZMod 2) + (d : ZMod 2) * (↑u⁻¹ : ZMod 2))‖ :=
          norm_sum_le _ _
      _ = 1 := by simp only [stdAddChar_norm, sum_const, card_univ,
        ZMod.card_units, nsmul_eq_mul]; norm_num
      _ ≤ _ := by linarith
  by_cases ha : (a : ZMod p) = 0
  · have hd : ¬ (p : ℤ) ∣ d :=
      hprimitive.resolve_left (not_not.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha))
    rw [ha, completeKloosterman_prime_zero_left p d hd, norm_neg, norm_one]
    linarith
  by_cases hd : (d : ZMod p) = 0
  · have he : completeKloosterman p (a : ZMod p) d =
        completeKloosterman p (a : ZMod p) 0 := by
      simp only [completeKloosterman_eq, hd, Int.cast_zero]
    rw [he, completeKloosterman_prime_zero_frequency p _ ha, norm_neg, norm_one]
    linarith
  exact completeKloosterman_odd_prime_weil p hp2 (a : ZMod p) d ha hd

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
