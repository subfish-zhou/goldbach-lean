import MathlibNt.Wu2008DoubleSieve.FourthRowMotherMasked
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherBadPrime

/-! # Original negative N-windows, with precisely 2 B(f) + B(c) restored -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_window_subset (N d : ℕ) (a f : ℝ) :
    primeWindow (d * N) a f ⊆ primeWindow N a f := by
  rw [primeWindow_mul_eq_filter]
  exact filter_subset _ _

theorem fourthRowMother_tuples_mono {P Q : Finset ℕ} (hPQ : P ⊆ Q) {r : ℕ}
    (hr : r = 2 ∨ r = 3 ∨ r = 4) :
    fourthRowMotherTuples P r ⊆ fourthRowMotherTuples Q r := by
  rcases hr with rfl | rfl | rfl
  · apply image_subset_image
    exact filter_subset_filter _ (product_subset_product hPQ hPQ)
  · apply image_subset_image
    exact filter_subset_filter _ (product_subset_product hPQ (product_subset_product hPQ hPQ))
  · apply image_subset_image
    exact filter_subset_filter _
      (product_subset_product hPQ (product_subset_product hPQ (product_subset_product hPQ hPQ)))

theorem fourthRowMother_prefix_mono (N d : ℕ) (a b c f : ℝ) (cs : List ℕ)
    (hcs : cs.length = 2 ∨ cs.length = 3 ∨ cs.length = 4) :
    fourthRowMotherPrefixTerm N d (d * N) a b c f cs ≤
      fourthRowMotherPrefixTerm N d N a b c f cs := by
  apply sum_le_sum_of_subset_of_nonneg
    (fourthRowMother_tuples_mono (fourthRowMother_window_subset N d a f) hcs)
  intro l _ _
  split_ifs <;> positivity

theorem fourthRowMother_pair_mono (N d : ℕ) (a u v w : ℝ) :
    fourthRowMotherPair N d (d * N) a u v w ≤ fourthRowMotherPair N d N a u v w := by
  have hn (p q : ℕ) :
      0 ≤ (if p < q then (sourceSieveCount N (d * p * q) (d * N) a : ℝ) else 0) := by
    split_ifs
    · simp only [sourceSieveCount, Int.cast_natCast]
      positivity
    · norm_num
  unfold fourthRowMotherPair
  calc
    _ ≤ ∑ q ∈ primeWindow (d * N) v w, ∑ p ∈ primeWindow N a u,
        if p < q then (sourceSieveCount N (d * p * q) (d * N) a : ℝ) else 0 := by
      apply sum_le_sum
      intro q _
      exact sum_le_sum_of_subset_of_nonneg (fourthRowMother_window_subset N d a u)
        (fun p _ _ => hn p q)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fourthRowMother_window_subset N d v w)
      (fun q _ _ => sum_nonneg fun p _ => hn p q)

theorem fourthRowMother_nine_mono (N d : ℕ) (b f : ℝ) :
    fourthRowMotherNine N d (d * N) b f ≤ fourthRowMotherNine N d N b f := by
  rw [fourthRowMother_nine_ordered, fourthRowMother_nine_ordered]
  have hw := fourthRowMother_window_subset N d b f
  apply sum_le_sum_of_subset_of_nonneg
    (filter_subset_filter _ (product_subset_product hw (product_subset_product hw hw)))
  intro t _ _
  simp only [sourceSieveCount, Int.cast_natCast]
  positivity

theorem fourthRowMother_restore_windows (N d : ℕ) (a b c f : ℝ) :
    fourthRowMotherLocal N d (d * N) a b c f ≤
      fourthRowMotherLocal N d N a b c f +
        2 * fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c := by
  have h5 := fourthRowMother_pair_mono N d a c a c
  have h6 := fourthRowMother_pair_mono N d a b c f
  have h7 := fourthRowMother_prefix_mono N d a b c f [0, 0] (by simp)
  have h8 := fourthRowMother_prefix_mono N d a b c f [0, 1] (by simp)
  have h9 := fourthRowMother_nine_mono N d b f
  have h10 := fourthRowMother_prefix_mono N d a b c f [1, 1, 2] (by simp)
  have h11 := fourthRowMother_prefix_mono N d a b c f [1, 2, 2] (by simp)
  have h13 := fourthRowMother_prefix_mono N d a b c f [0, 1, 2] (by simp)
  have h14 := fourthRowMother_prefix_mono N d a b c f [0, 2, 2] (by simp)
  have h16 := fourthRowMother_prefix_mono N d a b c f [2, 2, 2, 2] (by simp)
  have hf := fourthRowMother_negative_split N d a f
  have hc := fourthRowMother_negative_split N d a c
  unfold fourthRowMotherLocal
  linarith

theorem fourthRowMother_original_windows (N d : ℕ) {a b c f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcf : c ≤ f) :
    5 * (sourceSieveCount N d (d * N) f : ℝ) ≤
      fourthRowMotherLocal N d N a b c f +
        2 * fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c :=
  (fourthRowMother_masked N d hab hbc hcf).trans (fourthRowMother_restore_windows N d a b c f)

end Wu2008DoubleSieve
