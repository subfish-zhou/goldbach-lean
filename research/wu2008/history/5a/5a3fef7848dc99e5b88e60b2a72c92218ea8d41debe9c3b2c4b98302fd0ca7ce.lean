import SrcSingleSevenForcing

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Real Finset
open scoped Classical BigOperators

def primeBlock (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
    (sieveCount N p N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ)
def sevenBoundary (k : ℕ) : ℝ :=
  if k = 0 then 1 / 3 else 1 / 2 - truncatedSixthLowerAlpha * sourceNode (2 + k)

theorem prime_block_add {N : ℕ} (hN : 2 ≤ N) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    primeBlock N a b + primeBlock N b c = primeBlock N a c := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h := sum_primeWindow_split N (rpow_le_rpow_of_exponent_le hN1 hab)
    (rpow_le_rpow_of_exponent_le hN1 hbc)
    (fun p => sieveCount N p N ((N : ℝ) ^ truncatedSixthLowerAlpha))
  have hr := congrArg (fun x : ℤ => (x : ℝ)) h
  push_cast at hr
  exact hr.symm

theorem prime_block_self (N : ℕ) (a : ℝ) : primeBlock N a a = 0 := by
  apply sum_eq_zero
  intro p hp
  have hm := mem_primeWindow.mp hp
  exact False.elim (not_lt_of_ge hm.2.2.1 hm.2.2.2)

theorem seven_boundary_step {k : ℕ} (hk : k < 7) :
    sevenBoundary (k + 1) ≤ sevenBoundary k := by
  by_cases hz : k = 0
  · subst k
    norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]
  · simp only [sevenBoundary, if_neg hz, Nat.succ_ne_zero, if_false,
      sourceNode, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    norm_num [truncatedSixthLowerAlpha]
    linarith

theorem seven_boundary_le_top {k : ℕ} (hk : k ≤ 7) :
    sevenBoundary k ≤ sevenBoundary 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (seven_boundary_step (by omega)).trans (ih (by omega))

theorem seven_blocks_telescope {N : ℕ} (hN : 2 ≤ N) {n : ℕ} (hn : n ≤ 7) :
    (∑ k ∈ range n, primeBlock N (sevenBoundary (k + 1)) (sevenBoundary k)) =
      primeBlock N (sevenBoundary n) (sevenBoundary 0) := by
  induction n with
  | zero => simp [prime_block_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h := prime_block_add hN (seven_boundary_step (by omega))
      (seven_boundary_le_top (by omega : n ≤ 7))
    linarith only [h]

theorem psi_count_eq_block (j : Fin 7) (N : ℕ) :
    psiCount j N = primeBlock N (sevenBoundary (j.val + 1)) (sevenBoundary j.val) := by
  have hl : psiLeft j = sevenBoundary (j.val + 1) := by
    simp only [psiLeft, psiNode, sevenBoundary, Nat.succ_ne_zero, if_false]
    rw [show 2 + (j.val + 1) = 3 + j.val by omega]
  rw [psiCount, psiPrimes, hl]
  rfl

theorem seven_actual_partition {N : ℕ} (hN : 2 ≤ N) :
    (∑ j : Fin 7, psiCount j N) =
      primeBlock N (1 / 2 - truncatedSixthLowerAlpha * sourceNode 9) (1 / 3) := by
  have h := seven_blocks_telescope hN (n := 7) le_rfl
  simp_rw [psi_count_eq_block]
  have hsum : (∑ j : Fin 7,
      primeBlock N (sevenBoundary (j.val + 1)) (sevenBoundary j.val)) =
      ∑ k ∈ range 7, primeBlock N (sevenBoundary (k + 1)) (sevenBoundary k) := by
    simp [Fin.sum_univ_succ, Finset.sum_range_succ]
    ring
  rw [hsum, h]
  norm_num [sevenBoundary]

theorem third_actual_partition {N : ℕ} (hN : 2 ≤ N) :
    (SingleUpperCounts.U N (1 / 3) : ℝ) =
      primeBlock N truncatedSixthLowerAlpha
        (1 / 2 - truncatedSixthLowerAlpha * sourceNode 9) +
      ∑ j : Fin 7, psiCount j N := by
  rw [seven_actual_partition hN]
  have h := prime_block_add hN
    (by norm_num [truncatedSixthLowerAlpha, sourceNode] :
      truncatedSixthLowerAlpha ≤ 1 / 2 - truncatedSixthLowerAlpha * sourceNode 9)
    (by norm_num [truncatedSixthLowerAlpha, sourceNode] :
      1 / 2 - truncatedSixthLowerAlpha * sourceNode 9 ≤ (1 / 3 : ℝ))
  rw [h]
  unfold SingleUpperCounts.U primeBlock
  push_cast
  rfl

theorem third_fourth_finite_ledger {N : ℕ} (hN : 2 ≤ N) :
    (SingleUpperCounts.U N (1 / 3) : ℝ) +
        (SingleUpperCounts.U N truncatedSixthLowerSigma : ℝ) =
      primeBlock N truncatedSixthLowerAlpha
        (1 / 2 - truncatedSixthLowerAlpha * sourceNode 9) +
        (SingleUpperCounts.U N truncatedSixthLowerSigma : ℝ) +
      ∑ j : Fin 7, psiCount j N := by
  rw [third_actual_partition hN]
  ring

#check @seven_actual_partition
#check @third_fourth_finite_ledger
#print axioms seven_actual_partition
#print axioms third_fourth_finite_ledger
end WuSource.SrcSingle
