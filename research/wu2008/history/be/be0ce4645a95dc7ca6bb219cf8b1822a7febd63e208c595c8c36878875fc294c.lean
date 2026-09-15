import MathlibNt.Wu2008DoubleSieve.Omega3SieveDefinitions

/-!
# Full-label finite reordering of the actual closed X mass

Source: Wu 2004, arXiv TeX lines 2215–2238.  The triple is `(p1,p2,p3)`;
the varying `p3` endpoint is closed.  No cofactor image or uniqueness is used.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3XPrimes (N : ℕ) (δ s t : ℝ) (d : ℕ) :
    Finset (ℕ × ℕ × ℕ) :=
  ((primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) ×ˢ
    ((primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) ×ˢ
      (range (N + 1)))).filter fun p =>
        (p.1 : ℝ) < p.2.1 ∧ p.2.2.Prime ∧ p.2.1 < p.2.2 ∧
          (p.2.2 : ℝ) ≤ wuLocalCutoff N δ d s

theorem mem_omega3XPrimes {N d p1 p2 p3 : ℕ} {δ s t : ℝ} :
    (p1, p2, p3) ∈ omega3XPrimes N δ s t d ↔
      p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∧
      p1 ∈ primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ) ∧
      p3 ≤ N ∧ p3.Prime ∧ p2 < p3 ∧
      (p3 : ℝ) ≤ wuLocalCutoff N δ d s := by
  classical
  rw [omega3XPrimes, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  simp only [mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h12, hp3, h23, h3s⟩
    obtain ⟨hp1, hcop1, h1t, _⟩ := mem_primeWindow.mp h1
    exact ⟨h2, mem_primeWindow.mpr ⟨hp1, hcop1, h1t, h12⟩, h3, hp3, h23, h3s⟩
  · rintro ⟨h2, h1, h3, hp3, h23, h3s⟩
    obtain ⟨hp1, hcop1, h1t, h12⟩ := mem_primeWindow.mp h1
    exact ⟨⟨mem_primeWindow.mpr
      ⟨hp1, hcop1, h1t, h12.trans (mem_primeWindow.mp h2).2.2.2⟩, h2, h3⟩,
      h12, hp3, h23, h3s⟩

noncomputable def omega3XNCountFibre (N d p1 p2 p3 : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun n =>
    0 < n ∧ (d * p1 * p2 * p3) * n ≤ N ∧ Omega3Strengthened N d p1 p2 n

theorem mem_omega3XNCountFibre {N d p1 p2 p3 n : ℕ} :
    n ∈ omega3XNCountFibre N d p1 p2 p3 ↔
      n ≤ N ∧ 0 < n ∧ (d * p1 * p2 * p3) * n ≤ N ∧
        Omega3Strengthened N d p1 p2 n := by
  simp only [omega3XNCountFibre, mem_filter, mem_range, Nat.lt_succ_iff]

noncomputable def omega3XScale (N d p1 p2 p3 : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * p1 * p2 * p3)

/-- All five original labels and all gcd tests are retained in both directions. -/
theorem omega3X_full_label_iff {i N d p1 p2 p3 n : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} :
    ((⟨d, p2, p1, n⟩ : Omega3CofactorIndex) ∈ omega3CofactorLabels N δ s t W ∧
      p3 ∈ omega3CofactorPrimeFibreLE N δ s ⟨d, p2, p1, n⟩) ↔
    d ∈ boxConvolutionSupport W ∧ (p1, p2, p3) ∈ omega3XPrimes N δ s t d ∧
      n ∈ omega3XNCountFibre N d p1 p2 p3 := by
  have heq : omega3Cofactor d p1 p2 n * p3 = (d * p1 * p2 * p3) * n := by
    unfold omega3Cofactor
    ring
  classical
  rw [mem_omega3CofactorLabels, omega3CofactorPrimeFibreLE, Finset.mem_filter,
    Finset.mem_range]
  simp only [Nat.lt_succ_iff, omega3CofactorValue,
    mem_omega3XPrimes, mem_omega3XNCountFibre]
  constructor
  · rintro ⟨⟨hd, h2, h1, hnN, hn, _, hg⟩, h3N, h3, h23, h3s, hsize⟩
    exact ⟨hd, ⟨h2, h1, h3N, h3, h23, h3s⟩, hnN, hn, heq ▸ hsize, hg⟩
  · rintro ⟨hd, ⟨h2, h1, h3N, h3, h23, h3s⟩, hnN, hn, hsize, hg⟩
    have hs : omega3Cofactor d p1 p2 n * p3 ≤ N := heq.symm ▸ hsize
    exact ⟨⟨hd, h2, h1, hnN, hn,
      (Nat.mul_le_mul_left _ h23.le).trans hs, hg⟩, h3N, h3, h23, h3s, hs⟩

/-- Exact weighted full-label reordering, valid for arbitrary tests of the labels. -/
theorem omega3X_full_label_sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3CofactorIndex → ℕ → ℝ) :
    (∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
      ∑ p3 ∈ omega3CofactorPrimeFibreLE N δ s c, f c p3) =
    ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ p ∈ omega3XPrimes N δ s t d,
        ∑ n ∈ omega3XNCountFibre N d p.1 p.2.1 p.2.2,
          f ⟨d, p.2.1, p.1, n⟩ p.2.2 := by
  let A := (omega3CofactorLabels N δ s t W).sigma (omega3CofactorPrimeFibreLE N δ s)
  let B := (boxConvolutionSupport W).sigma fun d =>
    (omega3XPrimes N δ s t d).sigma fun p =>
      omega3XNCountFibre N d p.1 p.2.1 p.2.2
  change _ = ∑ d ∈ boxConvolutionSupport W, _
  rw [show (∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
      ∑ p3 ∈ omega3CofactorPrimeFibreLE N δ s c, f c p3) =
      ∑ a ∈ A, (convolutionCoeff W a.1.1 : ℝ) * f a.1 a.2 by
    simp only [A, sum_sigma, mul_sum]]
  rw [show (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ p ∈ omega3XPrimes N δ s t d,
        ∑ n ∈ omega3XNCountFibre N d p.1 p.2.1 p.2.2,
          f ⟨d, p.2.1, p.1, n⟩ p.2.2) =
      ∑ b ∈ B, (convolutionCoeff W b.1 : ℝ) *
        f ⟨b.1, b.2.1.2.1, b.2.1.1, b.2.2⟩ b.2.1.2.2 by
    simp only [B, sum_sigma, mul_sum]]
  apply sum_bij (fun a _ => ⟨a.1.1, (a.1.2.2.1, a.1.2.1, a.2), a.1.2.2.2⟩)
  · rintro ⟨⟨d, p2, p1, n⟩, p3⟩ ha
    simpa only [B, mem_sigma] using
      omega3X_full_label_iff.mp (mem_sigma.mp ha)
  · rintro ⟨⟨d, p2, p1, n⟩, p3⟩ _ ⟨⟨d', p2', p1', n'⟩, p3'⟩ _ he
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at he ⊢
    tauto
  · rintro ⟨d, ⟨p1, p2, p3⟩, n⟩ hb
    refine ⟨⟨⟨d, p2, p1, n⟩, p3⟩, ?_, rfl⟩
    apply mem_sigma.mpr
    apply omega3X_full_label_iff.mpr
    simpa only [B, mem_sigma] using hb
  · intro a _
    rfl

theorem omega3SieveX_eq_prime_triple_sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) :
    omega3SieveX N δ s t W =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ omega3XPrimes N δ s t d,
          ((omega3XNCountFibre N d p.1 p.2.1 p.2.2).card : ℝ) := by
  simpa only [sum_const, nsmul_eq_mul, mul_one, omega3SieveX] using
    omega3X_full_label_sum N δ s t W (fun _ _ => 1)

end Wu2008DoubleSieve
