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


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
