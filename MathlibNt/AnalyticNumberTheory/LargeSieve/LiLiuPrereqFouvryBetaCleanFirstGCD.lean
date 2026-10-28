import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModePayment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKLargeGCDExclusion
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanTail


/-!
# The original signed error reduced to the clean first-small-gcd truncation

The only retained oscillatory term has the actual original tuple domain,
the actual constructed cutoff, and the mask `gcd(n₁,n₂) ≤ x ^ η`.
The full truncation tail and the complementary first-large-gcd contribution
are paid after multiplication by alpha-squared. This is only the first gcd
exclusion: it is neither `WGCDData.Small` (all five gcds) nor IV.3.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Exact partition of the actual truncated tuple sum by the first gcd.
No coefficients, compatibility conditions, supports, or phases are changed. -/
theorem truncatedWNonzeroMode_eq_firstGCD_small_add_large
    (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    truncatedWNonzeroMode M H N Q β c a =
      wMaskedTruncated M H N Q β c a (fun t ↦ (t.2.1.gcd t.2.2 : ℝ) ≤ Y) +
        wMaskedTruncated M H N Q β c a (fun t ↦ Y < (t.2.1.gcd t.2.2 : ℝ)) := by
  rw [truncatedWNonzeroMode_eq_originalTuples]
  unfold wMaskedTruncated wMaskedTuples
  have hmask :
      (fun t : WOriginalTuple ↦ Y < (t.2.1.gcd t.2.2 : ℝ)) =
        (fun t : WOriginalTuple ↦ ¬((t.2.1.gcd t.2.2 : ℝ) ≤ Y)) := by
    funext t
    exact propext not_le.symm
  rw [hmask, sum_filter_add_sum_filter_not]

/-- Full signed decomposition, retaining the unmasked tail rather than
silently dropping frequencies on either side of the first-gcd partition. -/
theorem smoothWNonzeroMode_eq_firstGCD_small_add_large_add_tail
    (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    smoothWNonzeroMode M N Q β c a =
      wMaskedTruncated M H N Q β c a (fun t ↦ (t.2.1.gcd t.2.2 : ℝ) ≤ Y) +
        wMaskedTruncated M H N Q β c a (fun t ↦ Y < (t.2.1.gcd t.2.2 : ℝ)) +
          wMaskedTail M H N Q β c a (fun _ ↦ True) := by
  have h := smoothWNonzeroMode_sub_truncated_eq_full_tail M H N Q β c a
  rw [truncatedWNonzeroMode_eq_firstGCD_small_add_large M Y H N Q β c a] at h
  linarith


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
