import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompletion
import Mathlib.Data.ZMod.Units

/-!
# Twisted Chinese remaindering for the actual complete Kloosterman sum

The two twists are the integer Bezout coefficients: `m * gcdA m n +
n * gcdB m n = 1`. Thus `gcdB m n` is the inverse of `n` modulo `m`.
No frequency is required to be a unit, and either coprime factor may be one.
These are exact arithmetic identities, not an invocation of a Weil bound.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem stdAddChar_mul_modulus (q r : ℕ) [NeZero q] [NeZero r] (z : ℤ) :
    ZMod.stdAddChar ((r : ZMod (q * r)) * (z : ZMod (q * r))) =
      ZMod.stdAddChar (z : ZMod q) := by
  rw [← Int.cast_natCast r, ← Int.cast_mul, ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  field_simp

theorem zmod_map_inv_of_isUnit {q r : ℕ} (f : ZMod q →+* ZMod r)
    {u : ZMod q} (hu : IsUnit u) : f u⁻¹ = (f u)⁻¹ := by
  obtain ⟨v, rfl⟩ := hu
  rw [ZMod.inv_coe_unit]
  exact (Units.coe_map_inv f.toMonoidHom v).symm.trans
    (ZMod.inv_coe_unit (Units.map f.toMonoidHom v)).symm

theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (z : ZMod (m * n)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((m.gcdB n : ZMod m) * (ZMod.chineseRemainder h z).1) *
      ZMod.stdAddChar ((m.gcdA n : ZMod n) * (ZMod.chineseRemainder h z).2) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  have hab : (n : ℤ) * m.gcdB n + (m : ℤ) * m.gcdA n = 1 := by
    have hh := Nat.gcd_eq_gcd_ab m n
    rw [h.gcd_eq_one] at hh
    simpa only [Nat.cast_one, add_comm] using hh.symm
  have he : (a : ZMod (m * n)) =
      (n : ZMod (m * n)) * ((m.gcdB n * a : ℤ) : ZMod (m * n)) +
      (m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n)) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod (m * n))) (congrArg (· * a) hab)
    push_cast at hh
    push_cast
    linear_combination -hh
  have hn : ZMod.stdAddChar
      ((m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n))) =
      ZMod.stdAddChar ((m.gcdA n * a : ℤ) : ZMod n) := by
    rw [← Int.cast_natCast m, ← Int.cast_mul, ZMod.stdAddChar_coe,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
    field_simp
  calc
    _ = ZMod.stdAddChar
        ((n : ZMod (m * n)) * ((m.gcdB n * a : ℤ) : ZMod (m * n))) *
        ZMod.stdAddChar
        ((m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n))) := by
      rw [← AddChar.map_add_eq_mul, ← he]
    _ = _ := by
      rw [stdAddChar_mul_modulus, hn]
      simp only [map_intCast, Int.cast_mul, Prod.fst_intCast, Prod.snd_intCast]

/-- Multiplicativity with both frequencies twisted by the opposite modulus's inverse. -/
theorem completeKloosterman_crt (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a d : ℤ) :
    completeKloosterman (m * n) (a : ZMod (m * n)) d =
      completeKloosterman m ((a * m.gcdB n : ℤ) : ZMod m) (d * m.gcdB n) *
      completeKloosterman n ((a * m.gcdA n : ℤ) : ZMod n) (d * m.gcdA n) := by
  classical
  let e := ZMod.chineseRemainder h
  let f : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let g : ZMod (m * n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  have hu (u : ZMod (m * n)) : IsUnit u ↔ IsUnit (f u) ∧ IsUnit (g u) := by
    constructor
    · intro hh
      exact ⟨hh.map f, hh.map g⟩
    · intro hh
      have he : IsUnit (e u) := Prod.isUnit_iff.mpr hh
      simpa using he.map e.symm.toRingHom
  simp_rw [completeKloosterman_eq]
  rw [sum_mul]
  simp_rw [mul_sum]
  let F := fun p : ZMod m × ZMod n ↦
      (if IsUnit p.1 then ZMod.stdAddChar
        (((a * m.gcdB n : ℤ) : ZMod m) * p.1 +
          ((d * m.gcdB n : ℤ) : ZMod m) * p.1⁻¹) else 0) *
      (if IsUnit p.2 then ZMod.stdAddChar
        (((a * m.gcdA n : ℤ) : ZMod n) * p.2 +
          ((d * m.gcdA n : ℤ) : ZMod n) * p.2⁻¹) else 0)
  change _ = ∑ x : ZMod m, ∑ y : ZMod n, F (x, y)
  rw [← Fintype.sum_prod_type F]
  apply Fintype.sum_equiv e.toEquiv
  intro u
  change (if IsUnit u then _ else _) =
    (if IsUnit (f u) then _ else _) * (if IsUnit (g u) then _ else _)
  by_cases hunit : IsUnit u
  · have hfg := (hu u).mp hunit
    simp only [hunit, hfg.1, hfg.2, if_true]
    rw [stdAddChar_crt m n h]
    change ZMod.stdAddChar ((m.gcdB n : ZMod m) *
        f ((a : ZMod (m * n)) * u + (d : ZMod (m * n)) * u⁻¹)) *
      ZMod.stdAddChar ((m.gcdA n : ZMod n) *
        g ((a : ZMod (m * n)) * u + (d : ZMod (m * n)) * u⁻¹)) = _
    simp only [map_add, map_mul, map_intCast, zmod_map_inv_of_isUnit _ hunit,
      Int.cast_mul]
    rw [show f u = (e.toEquiv u).1 from rfl, show g u = (e.toEquiv u).2 from rfl]
    congr 2 <;> ring
  · have hfg := not_and_or.mp (mt (hu u).mpr hunit)
    rcases hfg with hf | hg
    · simp [hunit, hf]
    · simp [hunit, hg]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
