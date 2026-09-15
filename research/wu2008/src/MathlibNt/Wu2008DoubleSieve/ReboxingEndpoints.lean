import MathlibNt.Wu2008DoubleSieve.ReboxingPermutation

/-!
# The new box upper endpoint in Wu04 Proposition 2

Following (3.15), the reboxing endpoints satisfy
`(Q/prod V)^(1/t) <= alpha <= (Q/prod V)^(1/s)`.
For `2 <= s <= t <= 10` and fixed `0 < delta <= 1/10`, the actual
upper endpoint alpha satisfies the next lower-prime cutoff and the
full-product squared bound. This is stronger than the atomic `d*q^2<Q`
but still does not construct the sorted window family or boundary budgets.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

/-- In the source's sufficiently-small fixed-delta range, the original
box product leaves at least one full W_k factor of level, including depth zero. -/
theorem reboxing_box_level_ge_lower {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V) :
    (N : ℝ) ^ (δ ^ (k + 1)) ≤
      (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j) := by
  let w := (N : ℝ) ^ (δ ^ (k + 1))
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hw : 1 < w := one_lt_rpow hNr (pow_pos hδ _)
  have hV : ∀ j, w ≤ V j := hb.2.2.2.2.1
  have hprod : 0 < ∏ j, V j := prod_pos (fun j _ => lt_of_lt_of_le (by linarith) (hV j))
  apply (le_div_iff₀ hprod).2
  by_cases hi : i = 0
  · subst i
    simp only [Fin.prod_univ_zero, mul_one]
    apply rpow_le_rpow_of_exponent_le hNr.le
    have hp : δ ^ (k + 1) ≤ δ := by
      simpa only [pow_one] using
        pow_le_pow_of_le_one hδ.le (show δ ≤ 1 by linarith) (show 1 ≤ k + 1 by omega)
    linarith
  · have hp := boxSquaredPrefixes_product_mul_lower (Nat.pos_of_ne_zero hi)
      (by linarith : 0 ≤ w) hV hb.2.2.2.2.2
    simpa only [mul_comm] using hp

/-- A genuine box endpoint, not a selected prime, is above W_(k+1).
The restriction delta<=1/10 makes the source's `t<=10` argument valid. -/
theorem reboxing_endpoint_lower {i k N : ℕ} {δ Δ α t : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V) (ht : 0 < t) (ht10 : t ≤ 10)
    (hα : ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t) ≤ α) :
    (N : ℝ) ^ (δ ^ (k + 2)) ≤ α := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hδt : δ ≤ 1 / t := by
    apply (le_div_iff₀ ht).2
    nlinarith
  have hexp : δ ^ (k + 2) ≤ δ ^ (k + 1) * (1 / t) := by
    have hp := mul_le_mul_of_nonneg_left hδt (pow_nonneg hδ.le (k + 1))
    simpa only [show k + 2 = (k + 1) + 1 by omega, pow_succ] using hp
  calc
    _ ≤ (N : ℝ) ^ (δ ^ (k + 1) * (1 / t)) :=
      rpow_le_rpow_of_exponent_le hNr.le hexp
    _ = ((N : ℝ) ^ (δ ^ (k + 1))) ^ (1 / t) :=
      rpow_mul (by positivity : (0 : ℝ) ≤ N) _ _
    _ ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t) :=
      rpow_le_rpow (rpow_nonneg (by positivity) _)
        (reboxing_box_level_ge_lower hN hδ hδhi hb) (by positivity)
    _ ≤ α := hα

/-- The stronger full-product condition for an inserted box upper endpoint.
It is the scalar bound used before sorting in the source proof. -/
theorem reboxing_endpoint_squared_product {i k N : ℕ} {δ Δ α s : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hα0 : 0 ≤ α)
    (hα : α ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s)) :
    (∏ j, V j) * α ^ 2 ≤ (N : ℝ) ^ (1 / 2 - δ) := by
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hw : 1 < (N : ℝ) ^ (δ ^ (k + 1)) := one_lt_rpow hNr (pow_pos hδ _)
  have hq : 1 < q := hw.trans_le (reboxing_box_level_ge_lower hN hδ hδhi hb)
  have hprod : 0 < ∏ j, V j :=
    prod_pos (fun j _ => (by linarith : 0 < (N : ℝ) ^ (δ ^ (k + 1))).trans_le
      (hb.2.2.2.2.1 j))
  have hs0 : 0 < s := by linarith
  have hsqrt : α ^ 2 ≤ q := by
    calc
      _ ≤ (q ^ (1 / s)) ^ (2 : ℕ) := pow_le_pow_left₀ hα0 hα 2
      _ = q ^ ((1 / s) * 2) := by
        rw [← rpow_natCast, ← rpow_mul (by linarith : 0 ≤ q)]
        norm_num
      _ ≤ q ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hq.le (by
          calc
            (1 / s) * 2 = 2 / s := by ring
            _ ≤ 1 := (div_le_one hs0).2 hs)
      _ = q := rpow_one q
  simpa only [mul_comm] using (le_div_iff₀ hprod).1 hsqrt

end Wu2008DoubleSieve
