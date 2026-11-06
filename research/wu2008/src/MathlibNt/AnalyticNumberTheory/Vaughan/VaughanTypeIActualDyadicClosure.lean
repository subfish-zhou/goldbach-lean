

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIActualDyadicDecomposition

/-!
 # Unconditional closure of the actual dyadic Vaughan Type-I input
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Summing the per-character long-row inequality with the AP weight gives the
complete first- and middle-row means. -/
private theorem apNormalizedVaughanTypeIMean_le_complete_rows
    (N Q u v : ℕ) :
    apNormalizedVaughanTypeIMean N Q u v ≤
      apNormalizedVaughanTypeIFirstShellMean (Finset.Icc 1 u) N Q +
      apNormalizedVaughanTypeIMiddleProductShellMean
        (Finset.Icc 1 u ×ˢ Finset.Icc 1 v) N Q := by
  unfold apNormalizedVaughanTypeIMean apNormalizedPrimitiveMean
  unfold apNormalizedVaughanTypeIFirstShellMean
    apNormalizedVaughanTypeIMiddleProductShellMean
    apNormalizedWeightedRowShellMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun χ _ =>
      primitivePrefixAmplitude_vaughanTypeI_le_rows N u v q χ
  · positivity

/-- The first shell means sum exactly to the complete first-row mean. -/
private theorem sum_apNormalizedVaughanTypeIFirstDyadicShellMean
    (N Q u : ℕ) :
    (∑ k ∈ Finset.range (Nat.log2 u + 1),
      apNormalizedVaughanTypeIFirstShellMean
        (vaughanTypeIFirstDyadicShell u k) N Q) =
      apNormalizedVaughanTypeIFirstShellMean (Finset.Icc 1 u) N Q := by
  unfold apNormalizedVaughanTypeIFirstShellMean
    apNormalizedWeightedRowShellMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact sum_vaughanTypeIFirstDyadicShell u (fun d =>
    ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0
          (vaughanTypeIFirstRowLength N d) q χ))

/-- The product-dyadic middle shell means sum exactly to the complete middle-row mean. -/
private theorem sum_apNormalizedVaughanTypeIMiddleProductDyadicShellMean
    (N Q u v : ℕ) :
    (∑ k ∈ Finset.range (Nat.log2 (u * v) + 1),
      apNormalizedVaughanTypeIMiddleProductShellMean
        (vaughanTypeIMiddleProductDyadicShell u v k) N Q) =
      apNormalizedVaughanTypeIMiddleProductShellMean
        (Finset.Icc 1 u ×ˢ Finset.Icc 1 v) N Q := by
  unfold apNormalizedVaughanTypeIMiddleProductShellMean
    apNormalizedWeightedRowShellMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact sum_vaughanTypeIMiddleProductDyadicShell u v (fun de =>
    ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ))‖ *
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
          (vaughanTypeIMiddlePairRowLength N de) q χ))

/-- Exact unconditional decomposition of the AP-normalized Vaughan Type-I mean
into the actual first and product-dyadic middle shells. -/
theorem apNormalizedVaughanTypeIMean_le_actual_dyadic_shells
    (N Q u v : ℕ) :
    apNormalizedVaughanTypeIMean N Q u v ≤
      (∑ k ∈ Finset.range (Nat.log2 u + 1),
        apNormalizedVaughanTypeIFirstShellMean
          (vaughanTypeIFirstDyadicShell u k) N Q) +
      ∑ k ∈ Finset.range (Nat.log2 (u * v) + 1),
        apNormalizedVaughanTypeIMiddleProductShellMean
          (vaughanTypeIMiddleProductDyadicShell u v k) N Q := by
  rw [sum_apNormalizedVaughanTypeIFirstDyadicShellMean,
    sum_apNormalizedVaughanTypeIMiddleProductDyadicShellMean]
  exact apNormalizedVaughanTypeIMean_le_complete_rows N Q u v

/-- Primitive characters form a subtype of all Dirichlet characters, so their
cardinality is bounded by Euler's totient without any additional hypothesis. -/
theorem card_primitiveCharacter_le_totient (q : ℕ) :
    0 < q → Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  intro hq
  exact primitiveCharacter_card_le_totient_basic q hq


end

end AnalyticNumberTheory.LargeSieve
