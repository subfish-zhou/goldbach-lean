import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceGeometry

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSource
open Finset SecondFunctionalUnitPrimeFibre

/-- Original sigma coefficients, once each, and the literal N/d physical envelope. -/
theorem source_le20 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a2 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    FourPrimeUnit.source N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word20 ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R d^b d)).card : ℝ) := by
  unfold FourPrimeUnit.source
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (prefix_le20 (hdpos d hd) (hR d hd)
    (hlow d hd) (hb d hd)) (Nat.cast_nonneg _)

/-- The same bound applied to the accepted, fully labelled source representation. -/
theorem labels_le20 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a2 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    (∑ x ∈ FourPrimeUnit.labels N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word20,
        (convolutionCoeff W x.1 : ℝ)) ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R d^b d)).card : ℝ) := by
  rw [← FourPrimeUnit.source_labels]
  exact source_le20 hdpos hR hlow hb

/-- Weighted literal Gamma identity, with M=N and the unchanged prefix carrier. -/
theorem weighted_partition20 {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a B c e f : ℕ → ℝ) :
    FourPrimeUnit.source N W a B c e f word20 +
      (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        FourPrimeUnit.prefixTerm false N d (a d) (B d) (c d) (e d) (f d) word20) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        secondFunctionalMotherGamma N d N (a d) (B d) (c d) (e d) (f d) 20 := by
  unfold FourPrimeUnit.source
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← mul_add, partition20]

/-- Zero width empties the selected strict prefix, not an unrelated closed last-prime atom. -/
theorem source_zero20_left {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a2 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2)
    (heq : ∀ d ∈ boxConvolutionSupport W, a2 d = a3 d) :
    FourPrimeUnit.source N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word20 = 0 := by
  have h := source_le20 (N := N) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    hdpos hR hlow hb
  have hz : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R d^b d)).card : ℝ)) = 0 := by
    apply sum_eq_zero
    intro d hd
    rw [heq d hd, HighUnit.primePrefix20_empty_left (hR d hd)]
    simp
  rw [hz] at h
  exact le_antisymm h (FourPrimeUnit.source_nonneg _ _ _ _ _ _ _ _)

/-- Zero width empties the selected strict prefix, not an unrelated closed last-prime atom. -/
theorem source_zero20_right {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a2 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2)
    (heq : ∀ d ∈ boxConvolutionSupport W, a3 d = b d) :
    FourPrimeUnit.source N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word20 = 0 := by
  have h := source_le20 (N := N) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    hdpos hR hlow hb
  have hz : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R d^b d)).card : ℝ)) = 0 := by
    apply sum_eq_zero
    intro d hd
    rw [heq d hd, HighUnit.primePrefix20_empty_right (hR d hd)]
    simp
  rw [hz] at h
  exact le_antisymm h (FourPrimeUnit.source_nonneg _ _ _ _ _ _ _ _)

/-- Original sigma coefficients, once each, and the literal N/d physical envelope. -/
theorem source_le21 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a3 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    FourPrimeUnit.source N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word21 ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix21 (R d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 4)).val (R d^b d)).card : ℝ) := by
  unfold FourPrimeUnit.source
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (prefix_le21 (hdpos d hd) (hR d hd)
    (hlow d hd) (hb d hd)) (Nat.cast_nonneg _)

/-- The same bound applied to the accepted, fully labelled source representation. -/
theorem labels_le21 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a3 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    (∑ x ∈ FourPrimeUnit.labels N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word21,
        (convolutionCoeff W x.1 : ℝ)) ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix21 (R d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 4)).val (R d^b d)).card : ℝ) := by
  rw [← FourPrimeUnit.source_labels]
  exact source_le21 hdpos hR hlow hb

/-- Weighted literal Gamma identity, with M=N and the unchanged prefix carrier. -/
theorem weighted_partition21 {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a B c e f : ℕ → ℝ) :
    FourPrimeUnit.source N W a B c e f word21 +
      (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        FourPrimeUnit.prefixTerm false N d (a d) (B d) (c d) (e d) (f d) word21) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        secondFunctionalMotherGamma N d N (a d) (B d) (c d) (e d) (f d) 21 := by
  unfold FourPrimeUnit.source
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← mul_add, partition21]

/-- Zero width empties the selected strict prefix, not an unrelated closed last-prime atom. -/
theorem source_zero21_right {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a3 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2)
    (heq : ∀ d ∈ boxConvolutionSupport W, a3 d = b d) :
    FourPrimeUnit.source N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word21 = 0 := by
  have h := source_le21 (N := N) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    hdpos hR hlow hb
  have hz : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix21 (R d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 4)).val (R d^b d)).card : ℝ)) = 0 := by
    apply sum_eq_zero
    intro d hd
    rw [heq d hd, HighUnit.primePrefix21_empty (hR d hd)]
    simp
  rw [hz] at h
  exact le_antisymm h (FourPrimeUnit.source_nonneg _ _ _ _ _ _ _ _)

end Wu2008DoubleSieve.HighUnitSource
