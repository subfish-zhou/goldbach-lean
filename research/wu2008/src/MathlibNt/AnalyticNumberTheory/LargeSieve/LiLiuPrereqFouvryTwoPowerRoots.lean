import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimeSquare
import Mathlib.Data.Int.NatPrime

/-!
# Four-root bound over powers of two

If two unit roots have equal squares modulo `2^(n+1)`, their reductions
modulo `2^n` agree up to sign. Each of these two reduction fibers has size
two. The proof uses only divisibility of the difference of squares.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem two_power_dvd_factor (n : ℕ) (x y : ℤ)
    (hx : ¬ 4 ∣ x) (hxy : (2 : ℤ) ^ (n + 1) ∣ x * y) :
    (2 : ℤ) ^ n ∣ y := by
  by_cases hx2 : (2 : ℤ) ∣ x
  · obtain ⟨z, rfl⟩ := hx2
    have hz : ¬ (2 : ℤ) ∣ z := by
      rintro ⟨w, rfl⟩
      apply hx
      exact ⟨w, by ring⟩
    have hh : (2 : ℤ) ^ n ∣ z * y := by
      apply (mul_dvd_mul_iff_left (show (2 : ℤ) ≠ 0 by norm_num)).mp
      simpa only [pow_succ', mul_assoc] using hxy
    exact Int.prime_two.pow_dvd_of_dvd_mul_left n hz hh
  · exact (pow_dvd_pow 2 (Nat.le_succ n)).trans
      (Int.prime_two.pow_dvd_of_dvd_mul_left (n + 1) hx2 hxy)

private theorem two_power_square_congruence (n : ℕ) (x y : ℤ)
    (hy : ¬ (2 : ℤ) ∣ y) (hxy : (2 : ℤ) ^ (n + 1) ∣ x ^ 2 - y ^ 2) :
    (2 : ℤ) ^ n ∣ x - y ∨ (2 : ℤ) ^ n ∣ x + y := by
  have hp : (2 : ℤ) ^ (n + 1) ∣ (x - y) * (x + y) := by
    convert hxy using 1
    ring
  by_cases hm : (4 : ℤ) ∣ x - y
  · have hn : ¬ (4 : ℤ) ∣ x + y := by
      intro hn
      obtain ⟨u, hu⟩ := hm
      obtain ⟨v, hv⟩ := hn
      exact hy ⟨v - u, by omega⟩
    exact Or.inl (two_power_dvd_factor n (x + y) (x - y) hn
      (by simpa only [mul_comm] using hp))
  · exact Or.inr (two_power_dvd_factor n (x - y) (x + y) hm hp)

/-- A unit quadratic congruence with odd leading coefficient has at most four
roots modulo any positive power of two. -/
theorem two_power_unit_quadratic_root_card_le_four (n : ℕ) (a d : ℤ)
    (ha : ¬ (2 : ℤ) ∣ a) :
    (univ.filter fun v : ZMod (2 ^ n * 2) ↦
      IsUnit v ∧ (a : ZMod (2 ^ n * 2)) * v ^ 2 = (d : ZMod (2 ^ n * 2))).card ≤
      4 := by
  classical
  let s := univ.filter fun v : ZMod (2 ^ n * 2) ↦
    IsUnit v ∧ (a : ZMod (2 ^ n * 2)) * v ^ 2 = (d : ZMod (2 ^ n * 2))
  let f := ZMod.castHom (Nat.dvd_mul_right (2 ^ n) 2) (ZMod (2 ^ n))
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective v
    have hv' := (mem_filter.mp hv).2
    have hy : ¬ (2 : ℤ) ∣ y := by
      intro hy
      have hunit := hv'.1.map
        (ZMod.castHom (show 2 ∣ 2 ^ n * 2 from dvd_mul_left 2 _) (ZMod 2))
      have hz : (y : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd y 2).mpr hy
      exact hunit.ne_zero (by simpa only [map_intCast] using hz)
    have hsub : s ⊆ univ.filter fun u ↦ f u ∈ ({f (y : ZMod (2 ^ n * 2)),
        -f (y : ZMod (2 ^ n * 2))} : Finset (ZMod (2 ^ n))) := by
      intro u hu
      obtain ⟨x, rfl⟩ := ZMod.intCast_surjective u
      have hu' := (mem_filter.mp hu).2
      have hz : ((a * (x ^ 2 - y ^ 2) : ℤ) : ZMod (2 ^ n * 2)) = 0 := by
        push_cast
        linear_combination hu'.2 - hv'.2
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      have hsq : (2 : ℤ) ^ (n + 1) ∣ x ^ 2 - y ^ 2 := by
        apply Int.prime_two.pow_dvd_of_dvd_mul_left (n + 1) ha
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ] using hdvd
      have he := two_power_square_congruence n x y hy hsq
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        f, map_intCast]
      rcases he with hm | hp
      · left
        apply sub_eq_zero.mp
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) (2 ^ n)).mpr
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hm)
        simpa only [Int.cast_sub] using this
      · right
        apply eq_neg_iff_add_eq_zero.mpr
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) (2 ^ n)).mpr
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hp)
        simpa only [Int.cast_add] using this
    have hc := card_le_card hsub
    rw [zmod_reduction_preimage_card] at hc
    have hcard : ({f (y : ZMod (2 ^ n * 2)),
        -f (y : ZMod (2 ^ n * 2))} : Finset (ZMod (2 ^ n))).card ≤ 2 :=
      (card_insert_le _ _).trans (by simp)
    exact hc.trans (Nat.mul_le_mul_right 2 hcard)
  · change s.card ≤ 4
    rw [not_nonempty_iff_eq_empty.mp hs]
    simp

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
