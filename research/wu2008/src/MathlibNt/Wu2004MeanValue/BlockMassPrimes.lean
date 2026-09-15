import MathlibNt.Wu2004MeanValue.ManuscriptPairs
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# A uniformly bounded reciprocal-prime mass for actual block sources

For real `H >= 4`, use the natural scale `floor H`.  The actual source embeds
in the prime interval `((floor H)^(1/4), floor H]`.  Frozen Mertens bounds this
larger interval uniformly, so all coprimality and moving-endpoint restrictions
can safely be retained in the original source.
-/

namespace Wu2004MeanValue

open Finset
open MathlibNt.SieveTheory.MertensTheorem

theorem blockSource_prime_window {H : ℝ} {N m : ℕ} {a η : ℝ}
    (hH : 4 ≤ H) (ha : 3 / 2 < a) (hm : m ∈ blockSource H N a η) :
    m.Prime ∧ (⌊H⌋₊ : ℝ) ^ (1 / 4 : ℝ) < m ∧ (m : ℝ) ≤ ⌊H⌋₊ := by
  have hs := mem_blockSource.mp hm
  refine ⟨hs.1, ?_, ?_⟩
  · calc
      (⌊H⌋₊ : ℝ) ^ (1 / 4 : ℝ) ≤ H ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith))
          (by norm_num)
      _ ≤ H ^ ((a - 1) / a) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        apply (le_div_iff₀ (show 0 < a by linarith)).mpr
        linarith
      _ < m := hs.2.2.1
  · have hroot : Real.sqrt (2 * H) ≤ H - 1 := by
      have hsq := Real.sq_sqrt (show 0 ≤ 2 * H by linarith)
      have hr := Real.sqrt_nonneg (2 * H)
      nlinarith [mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ H - 4 by linarith)]
    have hf := Nat.lt_floor_add_one H
    exact hs.2.2.2.1.trans (hroot.trans (by linarith))

/-- A single positive bound precedes all real scales, all `N`, all moving
cutoffs `eta`, and even all `a > 3/2`. -/
theorem blockSource_reciprocal_sum_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 4 ≤ H →
      ∀ (N : ℕ) (a η : ℝ), 3 / 2 < a →
        (∑ m ∈ blockSource H N a η, 1 / (m : ℝ)) ≤ C := by
  obtain ⟨C, hC⟩ := prime_reciprocal_sum_bounded
    (1 / 4 : ℝ) 1 (by norm_num) (by norm_num)
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro H hH N a η ha
  let S : Finset ℕ := (range (⌊H⌋₊ + 1)).filter
    (fun p => p.Prime ∧
      ((⌊H⌋₊ : ℝ) ^ (1 / 4 : ℝ) < p ∧ (p : ℝ) ≤ (⌊H⌋₊ : ℝ) ^ (1 : ℝ)))
  have hsub : blockSource H N a η ⊆ S := by
    intro m hm
    have hw := blockSource_prime_window hH ha hm
    have hmf : m ≤ ⌊H⌋₊ := by exact_mod_cast hw.2.2
    simp only [S, mem_filter, mem_range, Real.rpow_one]
    exact ⟨by omega, hw⟩
  have hf : 2 ≤ ⌊H⌋₊ :=
    (Nat.le_floor_iff (show 0 ≤ H by linarith)).mpr (by norm_num; linarith)
  calc
    (∑ m ∈ blockSource H N a η, 1 / (m : ℝ)) ≤ ∑ m ∈ S, 1 / (m : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ |∑ m ∈ S, 1 / (m : ℝ)| := le_abs_self _
    _ ≤ C := hC ⌊H⌋₊ hf
    _ ≤ |C| + 1 := by linarith [le_abs_self C]

end Wu2004MeanValue
