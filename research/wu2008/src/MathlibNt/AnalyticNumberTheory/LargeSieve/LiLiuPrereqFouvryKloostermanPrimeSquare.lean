import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanStationary
import Mathlib.GroupTheory.Index

/-!
# Unconditional square-root cancellation at prime-square moduli

The stationary-phase identity is evaluated using equal-sized reduction
fibers and the two-root bound in a field. This proves the primitive
prime-square case, including `p=2`; the prime-modulus Weil theorem is not used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem zmod_reduction_fiber_card (q r : ℕ) [NeZero q] [NeZero r] (v : ZMod q) :
    (univ.filter fun u : ZMod (q * r) ↦
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) u = v).card = r := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  have hf := ZMod.castHom_surjective (Nat.dvd_mul_right q r)
  have hc (w : ZMod q) :
      (univ.filter fun u : ZMod (q * r) ↦ f u = w).card =
        (univ.filter fun u : ZMod (q * r) ↦ f u = v).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hf w) (hf v)
  have hsum := sum_card_fiberwise_eq_card_filter
    (univ : Finset (ZMod (q * r))) (univ : Finset (ZMod q)) f
  simp only [hc, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mem_univ,
    filter_true] at hsum
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos q) hsum

theorem zmod_reduction_preimage_card (q r : ℕ) [NeZero q] [NeZero r]
    (s : Finset (ZMod q)) :
    (univ.filter fun u : ZMod (q * r) ↦
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) u ∈ s).card = s.card * r := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter, sum_congr rfl (fun v _ ↦
    zmod_reduction_fiber_card q r v), sum_const, nsmul_eq_mul]
  rfl

theorem completeKloosterman_square_modulus_norm_le_roots (m : ℕ) [NeZero m]
    (a d : ℤ) :
    ‖completeKloosterman (m * m) (a : ZMod (m * m)) d‖ ≤
      (m : ℝ) * ((univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 =
        (d : ZMod m)).card : ℝ) := by
  classical
  refine (completeKloosterman_square_modulus_norm_le m a d).trans ?_
  let s := univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)
  have hle : (univ.filter fun u : ZMod (m * m) ↦ IsUnit u ∧
      (a : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 =
        (d : ZMod m)).card ≤
      (univ.filter fun u : ZMod (m * m) ↦
        ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u ∈ s).card := by
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_univ, true_and, s] at hu ⊢
    exact hu.2
  rw [zmod_reduction_preimage_card] at hle
  exact_mod_cast (hle.trans_eq (Nat.mul_comm s.card m))

theorem prime_quadratic_root_card_le_two (p : ℕ) [Fact p.Prime]
    (a d : ZMod p) (ha : a ≠ 0) :
    (univ.filter fun v : ZMod p ↦ a * v ^ 2 = d).card ≤ 2 := by
  classical
  let s := univ.filter fun v : ZMod p ↦ a * v ^ 2 = d
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    have hv' : a * v ^ 2 = d := (mem_filter.mp hv).2
    have hsub : s ⊆ {v, -v} := by
      intro w hw
      have hw' := (mem_filter.mp hw).2
      have he : w ^ 2 = v ^ 2 := mul_left_cancel₀ ha (hw'.trans hv'.symm)
      simpa only [mem_insert, mem_singleton] using
        (sq_eq_sq_iff_eq_or_eq_neg.mp he)
    exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp))
  · have hz : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ 2
    rw [hz]
    simp

/-- A genuine square-root estimate, uniform in both frequencies, for primitive
prime-square pairs. This includes the prime two. -/
theorem completeKloosterman_prime_square_norm_le (p : ℕ) [Fact p.Prime]
    (a d : ℤ) (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p * p) (a : ZMod (p * p)) d‖ ≤ 2 * (p : ℝ) := by
  have bound (b c : ℤ) (hb : ¬ (p : ℤ) ∣ b) :
      ‖completeKloosterman (p * p) (b : ZMod (p * p)) c‖ ≤ 2 * (p : ℝ) := by
    have hroot := prime_quadratic_root_card_le_two p (b : ZMod p) (c : ZMod p)
      (fun hz ↦ hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hz))
    have hR : ((univ.filter fun v : ZMod p ↦ (b : ZMod p) * v ^ 2 =
        (c : ZMod p)).card : ℝ) ≤ 2 := by exact_mod_cast hroot
    exact (completeKloosterman_square_modulus_norm_le_roots p b c).trans
      ((mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg p)).trans_eq (mul_comm _ _))
  rcases hprimitive with ha | hd
  · exact bound a d ha
  · rw [completeKloosterman_symm]
    exact bound d a hd

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
