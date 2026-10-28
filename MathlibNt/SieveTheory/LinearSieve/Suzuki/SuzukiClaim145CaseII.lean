import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDiscreteParityRecurrence

open scoped Classical BigOperators Interval
open MeasureTheory Set Finset

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000

/-- For every odd source layer of index at least three, the weighted layer
`s f_n(s)` is constant on Suzuki's short initial interval. -/
theorem odd_layer_weighted_eq_at_beta_add_one
    {β s : ℝ} {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hs : 0 < s) (hsβ : s ≤ β + 1) :
    s * suzukiLayer 1 β n s =
      (β + 1) * suzukiLayer 1 β n (β + 1) := by
  obtain ⟨k, hk⟩ := hn
  have hkpos : 0 < k := by omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  subst k
  subst n
  let m : ℕ := 2 * j + 1
  have hnform : 2 * (j + 1) + 1 = m + 2 := by dsimp [m]; omega
  rw [hnform]
  have hbpos : 0 < β + 1 := hs.trans_le hsβ
  have hlower_s : recursionLower β s (m + 2) = β + 1 := by
    unfold recursionLower sourceEpsilon
    have hmod : (m + 2) % 2 = 1 := by dsimp [m]; omega
    rw [hmod]
    norm_num only [Nat.cast_one]
    rw [max_eq_right hsβ]
    apply min_eq_left
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    push_cast
    linarith
  have hlower_b : recursionLower β (β + 1) (m + 2) = β + 1 := by
    unfold recursionLower sourceEpsilon
    have hmod : (m + 2) % 2 = 1 := by dsimp [m]; omega
    rw [hmod]
    norm_num only [Nat.cast_one, max_self]
    apply min_eq_left
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    push_cast
    linarith
  calc
    s * suzukiLayer 1 β (m + 2) s =
        s ^ (1 : ℝ) * suzukiLayer 1 β (m + 2) s := by norm_num
    _ = suzukiLayerNumerator 1 β (m + 2) s :=
      rpow_mul_suzukiLayer 1 β (m + 2) hs
    _ = suzukiLayerNumerator 1 β (m + 2) (β + 1) := by
      rw [suzukiLayerNumerator_succ_succ, suzukiLayerNumerator_succ_succ,
        hlower_s, hlower_b]
    _ = (β + 1) ^ (1 : ℝ) * suzukiLayer 1 β (m + 2) (β + 1) :=
      (rpow_mul_suzukiLayer 1 β (m + 2) hbpos).symm
    _ = (β + 1) * suzukiLayer 1 β (m + 2) (β + 1) := by norm_num

/-- Exact κ=1 continuous identity used in Suzuki Case II:
`((β+1)/s) T_N(β+1) + T_1(s) = T_N(s)` for odd `N`. -/
theorem finiteSourceLayer_caseII_identity
    {β s : ℝ} {N : ℕ} (hN : Odd N)
    (hs : 0 < s) (hsβ : s ≤ β + 1) :
    ((β + 1) / s) * finiteSourceLayer 1 β N (β + 1) +
        finiteSourceLayer 1 β 1 s = finiteSourceLayer 1 β N s := by
  classical
  have hN1 : 1 ≤ N := by rcases hN with ⟨k, rfl⟩; omega
  have hpar : N % 2 = 1 := Nat.odd_iff.mp hN
  have hrepr (x : ℝ) : finiteSourceLayer 1 β N x =
      ∑ n ∈ sourceParityIndices N, suzukiLayer 1 β n x := by
    unfold finiteSourceLayer sourceParityIndices
    rw [hpar]
    simp only [Finset.sum_filter]
  have hone_mem : 1 ∈ sourceParityIndices N := by
    simp [sourceParityIndices, hN1, hpar]
  rw [hrepr, hrepr, finiteSourceLayer_one_eq_suzukiLayer]
  have hsplit_s := Finset.sum_erase_add (sourceParityIndices N)
    (fun n => suzukiLayer 1 β n s) hone_mem
  have hsplit_b := Finset.sum_erase_add (sourceParityIndices N)
    (fun n => suzukiLayer 1 β n (β + 1)) hone_mem
  rw [← hsplit_s, ← hsplit_b]
  have hbase_b : suzukiLayer 1 β 1 (β + 1) = 0 := by
    apply suzukiLayer_eq_zero_of_le 1 β 1
    norm_num
  rw [hbase_b, add_zero]
  have hsum : s * (∑ x ∈ (sourceParityIndices N).erase 1, suzukiLayer 1 β x s) =
      (β + 1) * (∑ x ∈ (sourceParityIndices N).erase 1,
        suzukiLayer 1 β x (β + 1)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hnmem
    have hnidx := Finset.mem_of_mem_erase hnmem
    have hnrange : 1 ≤ n ∧ n ≤ N := by
      exact Finset.mem_Icc.mp (Finset.mem_filter.mp hnidx).1
    have hnpar : n % 2 = 1 := (Finset.mem_filter.mp hnidx).2.trans hpar
    have hnodd : Odd n := Nat.odd_iff.mpr hnpar
    have hnneq : n ≠ 1 := (Finset.mem_erase.mp hnmem).1
    exact odd_layer_weighted_eq_at_beta_add_one hnodd (by omega) hs hsβ
  have hsne : s ≠ 0 := ne_of_gt hs
  field_simp [hsne]
  nlinarith


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
