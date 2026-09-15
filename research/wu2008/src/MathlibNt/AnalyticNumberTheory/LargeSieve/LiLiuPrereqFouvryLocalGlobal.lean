import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLocalGlobalPrimePower
import Mathlib.Data.Nat.Factorization.Induction

/-!
# From primitive prime powers to every nonzero modulus

Chinese remaindering twists both frequencies by a Bezout coefficient. Its
coprimality with the corresponding modulus preserves the full three-way gcd.
Together with exact common-factor descent this proves the all-modulus estimate
from a single explicitly quantified primitive prime-power input.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem localGlobal_bezout_coprime (m n : ℕ) (h : m.Coprime n) :
    m.Coprime (m.gcdB n).natAbs ∧ n.Coprime (m.gcdA n).natAbs := by
  have he : (m : ℤ) * m.gcdA n + (n : ℤ) * m.gcdB n = 1 := by
    simpa only [h.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab m n).symm
  have hb : IsCoprime (m : ℤ) (m.gcdB n) :=
    ⟨m.gcdA n, (n : ℤ), by simpa only [mul_comm] using he⟩
  have ha : IsCoprime (n : ℤ) (m.gcdA n) :=
    ⟨m.gcdB n, (m : ℤ), by simpa only [mul_comm, add_comm] using he⟩
  constructor
  · simpa only [Nat.coprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using
      Int.isCoprime_iff_gcd_eq_one.mp hb
  · simpa only [Nat.coprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using
      Int.isCoprime_iff_gcd_eq_one.mp ha

theorem localGlobal_gcd_twist (q : ℕ) (b a d : ℤ) (hb : q.Coprime b.natAbs) :
    q.gcd ((a * b).natAbs.gcd (d * b).natAbs) = q.gcd (a.natAbs.gcd d.natAbs) := by
  rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_right]
  exact hb.symm.gcd_mul_right_cancel_right _

theorem localGlobal_gcd_coprime_mul (m n g : ℕ) (h : m.Coprime n) :
    (m * n).gcd g = m.gcd g * n.gcd g := by
  simpa only [Nat.gcd_comm] using h.gcd_mul g

theorem localGlobal_weil_envelope_mul (m n g : ℕ) (h : m.Coprime n) :
    ((m * n).divisors.card : ℝ) * Real.sqrt ((m * n).gcd g) * Real.sqrt (m * n : ℕ) =
      ((m.divisors.card : ℝ) * Real.sqrt (m.gcd g) * Real.sqrt m) *
        ((n.divisors.card : ℝ) * Real.sqrt (n.gcd g) * Real.sqrt n) := by
  rw [h.card_divisors_mul, localGlobal_gcd_coprime_mul m n g h]
  simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg (m.gcd g)),
    Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

/-- Conditional all-modulus Weil bound, with signed frequencies, modulus one,
and zero or nonprimitive frequencies. Only primitive prime-power bounds are
assumed; coprime assembly and common-factor descent are proved. -/
theorem completeKloosterman_weil_of_primitive_prime_power
    (hlocal : ∀ (p k : ℕ) (_ : Fact p.Prime) (a d : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) * Real.sqrt q := by
  have hall : ∀ (q : ℕ) (_ : NeZero q) (a d : ℤ),
      ‖completeKloosterman q (a : ZMod q) d‖ ≤
        (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) *
          Real.sqrt q := by
    refine Nat.recOnPrimeCoprime ?_ ?_ ?_
    · intro hq
      exact False.elim (hq.out rfl)
    · intro p k hp hq a d
      let : Fact p.Prime := ⟨hp⟩
      rw [localGlobal_card_divisors_prime_power]
      exact completeKloosterman_prime_power_weil_of_primitive p
        (fun k a d ↦ hlocal p k inferInstance a d) k a d
    · intro m n hm hn hmn hmBound hnBound hq a d
      let : NeZero m := ⟨by omega⟩
      let : NeZero n := ⟨by omega⟩
      have htwist := localGlobal_bezout_coprime m n hmn
      rw [completeKloosterman_crt m n hmn, norm_mul]
      have hleft := hmBound inferInstance (a * m.gcdB n) (d * m.gcdB n)
      have hright := hnBound inferInstance (a * m.gcdA n) (d * m.gcdA n)
      rw [localGlobal_gcd_twist m _ a d htwist.1] at hleft
      rw [localGlobal_gcd_twist n _ a d htwist.2] at hright
      rw [localGlobal_weil_envelope_mul m n _ hmn]
      exact mul_le_mul hleft hright (norm_nonneg _) (by positivity)
  exact hall q inferInstance a d

/-- The residue-valued interface used by the existing Weil-to-Fouvry bridge. -/
theorem completeKloosterman_weil_zmod_of_primitive_prime_power
    (hlocal : ∀ (p k : ℕ) (_ : Fact p.Prime) (a d : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) :
    ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (m.val.gcd d.natAbs)) * Real.sqrt q := by
  simpa only [Int.natAbs_natCast, Int.cast_natCast, ZMod.natCast_zmod_val] using
    completeKloosterman_weil_of_primitive_prime_power hlocal q (m.val : ℤ) d

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
