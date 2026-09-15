import MathlibNt.Wu2008DoubleSieve.Omega3LabelsIndexed

/-!
# Cofactor labels separate from the varying switched prime

The cofactor index retains d,p2,p1,n, but not p3. Multiplicity bounds over e
must be applied to this index, not to the full switched-output index. The
independent p3 fibre has the literal strict upper endpoint.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

abbrev Omega3CofactorIndex := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

def omega3CofactorValue (c : Omega3CofactorIndex) : ℕ :=
  omega3Cofactor c.1 c.2.2.1 c.2.1 c.2.2.2

noncomputable def omega3CofactorLabels {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : Finset Omega3CofactorIndex :=
  (boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)).sigma fun p2 =>
      (primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ)).sigma fun p1 =>
        (range (N + 1)).filter fun n =>
          0 < n ∧ omega3Cofactor d p1 p2 n * p2 ≤ N ∧ Omega3Strengthened N d p1 p2 n

noncomputable def omega3CofactorPrimeFibre (N : ℕ) (δ s : ℝ)
    (c : Omega3CofactorIndex) : Finset ℕ :=
  (primeWindow N (c.2.1 : ℝ) (wuLocalCutoff N δ c.1 s)).filter fun p3 =>
    c.2.1 < p3 ∧ omega3CofactorValue c * p3 ≤ N

def omega3SeparatePrime (a : Omega3Index) : Σ _ : Omega3CofactorIndex, ℕ :=
  ⟨⟨a.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩, a.2.1⟩

def omega3RestorePrime (b : Σ _ : Omega3CofactorIndex, ℕ) : Omega3Index :=
  ⟨b.1.1, b.2, b.1.2.1, b.1.2.2.1, b.1.2.2.2⟩

theorem omega3_restore_separate (a : Omega3Index) :
    omega3RestorePrime (omega3SeparatePrime a) = a := by
  rcases a with ⟨d, p3, p2, p1, n⟩
  rfl

theorem omega3_separate_restore (b : Σ _ : Omega3CofactorIndex, ℕ) :
    omega3SeparatePrime (omega3RestorePrime b) = b := by
  rcases b with ⟨⟨d, p2, p1, n⟩, p3⟩
  rfl

theorem mem_omega3CofactorLabels {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {d p1 p2 n : ℕ} :
    (⟨d, p2, p1, n⟩ : Omega3CofactorIndex) ∈ omega3CofactorLabels N δ s t W ↔
      d ∈ boxConvolutionSupport W ∧
      p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∧
      p1 ∈ primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ) ∧
      n ≤ N ∧ 0 < n ∧ omega3Cofactor d p1 p2 n * p2 ≤ N ∧
      Omega3Strengthened N d p1 p2 n := by
  simp only [omega3CofactorLabels, mem_sigma, mem_filter, mem_range, Nat.lt_succ_iff]

theorem omega3_separate_prime_mem {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : Omega3Index} (ha : a ∈ omega3SwitchedLabels N δ s t W) :
    omega3SeparatePrime a ∈
      (omega3CofactorLabels N δ s t W).sigma (omega3CofactorPrimeFibre N δ s) := by
  rcases a with ⟨d, p3, p2, p1, n⟩
  obtain ⟨hd, h3, h2, h1, hn⟩ := mem_omega3SwitchedLabels.mp ha
  obtain ⟨hnN, hnpos, hsize, hgood⟩ := mem_filter.mp hn
  have h3' := mem_primeWindow.mp h3
  have h2' := mem_primeWindow.mp h2
  have h23 : p2 < p3 := by exact_mod_cast h2'.2.2.2
  apply mem_sigma.mpr
  constructor
  · apply mem_omega3CofactorLabels.mpr
    exact ⟨hd, mem_primeWindow.mpr ⟨h2'.1, h2'.2.1, h2'.2.2.1,
      h2'.2.2.2.trans h3'.2.2.2⟩, h1, Nat.le_of_lt_succ (mem_range.mp hnN),
      hnpos, (Nat.mul_le_mul_left _ h23.le).trans hsize, hgood⟩
  · apply mem_filter.mpr
    exact ⟨mem_primeWindow.mpr ⟨h3'.1, h3'.2.1, h2'.2.2.2.le, h3'.2.2.2⟩, h23, hsize⟩

theorem omega3_restore_prime_mem {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {b : Σ _ : Omega3CofactorIndex, ℕ}
    (hb : b ∈ (omega3CofactorLabels N δ s t W).sigma (omega3CofactorPrimeFibre N δ s)) :
    omega3RestorePrime b ∈ omega3SwitchedLabels N δ s t W := by
  rcases b with ⟨⟨d, p2, p1, n⟩, p3⟩
  obtain ⟨hc, h3⟩ := mem_sigma.mp hb
  obtain ⟨hd, h2, h1, hnN, hnpos, _, hgood⟩ := mem_omega3CofactorLabels.mp hc
  obtain ⟨h3, h23, hsize⟩ := mem_filter.mp h3
  have h3' := mem_primeWindow.mp h3
  have h2' := mem_primeWindow.mp h2
  have h23r : (p2 : ℝ) < p3 := by exact_mod_cast h23
  apply mem_omega3SwitchedLabels.mpr
  exact ⟨hd, mem_primeWindow.mpr ⟨h3'.1, h3'.2.1,
    h2'.2.2.1.trans h3'.2.2.1, h3'.2.2.2⟩,
    mem_primeWindow.mpr ⟨h2'.1, h2'.2.1, h2'.2.2.1, h23r⟩, h1,
    mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hnN), hnpos, hsize, hgood⟩⟩

/-- Exact cofactor-first reindexing with every test of the full switched
label retained. No p3 choice enters the cofactor fibre multiplicity. -/
theorem omega3_cofactor_first_sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3Index → ℝ) :
    (∑ a ∈ omega3SwitchedLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) * f a) =
      ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
        ∑ p3 ∈ omega3CofactorPrimeFibre N δ s c, f (omega3RestorePrime ⟨c, p3⟩) := by
  rw [show (∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
      ∑ p3 ∈ omega3CofactorPrimeFibre N δ s c, f (omega3RestorePrime ⟨c, p3⟩)) =
      ∑ b ∈ (omega3CofactorLabels N δ s t W).sigma (omega3CofactorPrimeFibre N δ s),
        (convolutionCoeff W b.1.1 : ℝ) * f (omega3RestorePrime b) by
    simp only [sum_sigma, mul_sum]]
  apply sum_bij (fun a _ => omega3SeparatePrime a)
  · exact fun _ ha => omega3_separate_prime_mem ha
  · intro a _ b _ hab
    simpa only [omega3_restore_separate] using congrArg omega3RestorePrime hab
  · intro b hb
    exact ⟨omega3RestorePrime b, omega3_restore_prime_mem hb, omega3_separate_restore b⟩
  · intro a _
    simp only [omega3_restore_separate]
    rfl

/-- The e-fibre of cofactor labels excludes the varying p3 coordinate. -/
theorem omega3_cofactor_label_fibres {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3CofactorIndex → ℝ) :
    (∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) * f c) =
      ∑ e ∈ (omega3CofactorLabels N δ s t W).image omega3CofactorValue,
        ∑ c ∈ (omega3CofactorLabels N δ s t W).filter (fun c => omega3CofactorValue c = e),
          (convolutionCoeff W c.1 : ℝ) * f c := by
  exact (sum_fiberwise_of_maps_to (fun _ hc => mem_image_of_mem _ hc) _).symm

theorem omega3_switched_sifted_cofactor_first {i : ℕ} (N : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) :
    omega3SwitchedSiftedCount N δ s t Z W =
      ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
        (((omega3CofactorPrimeFibre N δ s c).filter
          (fun p3 => Sifted N (N - omega3CofactorValue c * p3) Z)).card : ℝ) := by
  rw [omega3_switched_sifted_eq_indexed_count, sum_filter]
  have h := omega3_cofactor_first_sum N δ s t W
    (fun a => if Sifted N (omega3IndexOutput N a) Z then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  change (∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
    ∑ p3 ∈ omega3CofactorPrimeFibre N δ s c,
      if Sifted N (N - omega3CofactorValue c * p3) Z then (1 : ℝ) else 0) = _
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end Wu2008DoubleSieve
