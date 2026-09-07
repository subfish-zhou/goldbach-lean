import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWGCDReindex

/-!
# Poisson extraction with the same arithmetic mask

The exclusions in Fouvry (1984), (8.2)--(8.5), concern the original
progression sum, not its truncated nonzero frequencies. This module keeps
the same mask on the original sum, zero mode, retained frequencies and tail.
No estimate for an unmasked zero mode is restricted to a new subset.
-/

noncomputable section

open Classical

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wMaskedTuples (N Q : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop) :
    Finset WOriginalTuple :=
  (wOriginalTuples N Q a).filter P

def wTupleCoefficient (β c : ℕ → ℝ) (t : WOriginalTuple) : ℝ :=
  c t.1.1 * c t.1.2 * β t.2.1 * β t.2.2

def wMaskedOriginal (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) : ℝ :=
  ∑ t ∈ wMaskedTuples N Q a P, wTupleCoefficient β c t *
    productProgressionWeight (dyadicCutoffNatSupport M)
      (fun m ↦ scaledDyadicCutoff M m) a t.1.1 t.1.2 t.2.1 t.2.2

def wMaskedZeroMode (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) : ℝ :=
  ∑ t ∈ wMaskedTuples N Q a P, wTupleCoefficient β c t *
    ((M / (t.1.1.lcm t.1.2 : ℝ)) * dyadicCutoffMass)

def wMaskedTruncated (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) : ℝ :=
  ∑ t ∈ wMaskedTuples N Q a P, wOriginalTerm M H β c a t

def wMaskedTail (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) : ℝ :=
  ∑ t ∈ wMaskedTuples N Q a P, wTupleCoefficient β c t *
    ((∑' h : ℤ, wPoissonFrequency M a t.1.1 t.1.2 t.2.1 t.2.2 h) -
      ∑ h ∈ Finset.Icc (-(H t.1.1 t.1.2 : ℤ)) (H t.1.1 t.1.2),
        wPoissonFrequency M a t.1.1 t.1.2 t.2.1 t.2.2 h).re

def wMaskedTailEnvelope (k : ℕ) (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) : ℝ :=
  ∑ t ∈ wMaskedTuples N Q a P, |wTupleCoefficient β c t| /
    (1 + (M / (t.1.1.lcm t.1.2 : ℝ)) * H t.1.1 t.1.2) ^ k

theorem wMaskedTuples_spec {N Q : Finset ℕ} {a : ℤ} {P : WOriginalTuple → Prop}
    {t : WOriginalTuple} (ht : t ∈ wMaskedTuples N Q a P) :
    t.1.1 ∈ Q ∧ t.1.2 ∈ Q ∧
      WCompatible t.1.1 t.1.2 t.2.1 t.2.2 ∧ P t := by
  obtain ⟨ht, hP⟩ := Finset.mem_filter.mp ht
  obtain ⟨hs, hc⟩ := Finset.mem_filter.mp ht
  simp only [Finset.mem_product] at hs
  exact ⟨(Finset.mem_filter.mp hs.1.1).1,
    (Finset.mem_filter.mp hs.1.2).1, hc, hP⟩

/-- Exact extraction on any arithmetic subdomain, with no positivity
assumptions on the coefficients or restrictions on the changing residue. -/
theorem wMaskedOriginal_eq_zero_add_truncated_add_tail
    {M : ℝ} (hM : 0 < M) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    wMaskedOriginal M N Q β c a P =
      wMaskedZeroMode M N Q β c a P +
        wMaskedTruncated M H N Q β c a P + wMaskedTail M H N Q β c a P := by
  unfold wMaskedOriginal wMaskedZeroMode wMaskedTruncated wMaskedTail
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨hq, hr, hc, _⟩ := wMaskedTuples_spec ht
  rw [productProgressionWeight_eq_main_add_fourier hM a (hQ _ hq) (hQ _ hr) hc]
  simp only [wOriginalTerm, wTupleCoefficient, Complex.sub_re]
  ring

/-- The tail constant is chosen before the mask, all coefficients, both
supports, the residue, and the modulus-dependent frequency cutoffs. -/
theorem wMaskedTail_uniform (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ H : ℕ → ℕ → ℕ,
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ,
      ∀ P : WOriginalTuple → Prop, (∀ q ∈ Q, q ≠ 0) →
      |wMaskedTail M H N Q β c a P| ≤
        C * wMaskedTailEnvelope k M H N Q β c a P := by
  obtain ⟨C, hC, hb⟩ := wPoissonFrequency_truncation_error k
  refine ⟨C, hC, fun M hM H N Q β c a P hQ ↦ ?_⟩
  unfold wMaskedTail wMaskedTailEnvelope
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨hq, hr, _, _⟩ := wMaskedTuples_spec ht
  rw [abs_mul]
  calc
    _ ≤ |wTupleCoefficient β c t| *
        (C / (1 + (M / (t.1.1.lcm t.1.2 : ℝ)) * H t.1.1 t.1.2) ^ k) :=
      mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans
          (hb M hM _ _ (hQ _ hq) (hQ _ hr) a _ _ _)) (abs_nonneg _)
    _ = _ := by ring

/-- Transport a bound for an original progression sum only with its own
zero mode and its own tail, never with the unmasked SW main term. -/
theorem wMaskedTruncated_abs_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ H : ℕ → ℕ → ℕ,
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ,
      ∀ P : WOriginalTuple → Prop, (∀ q ∈ Q, q ≠ 0) →
      |wMaskedTruncated M H N Q β c a P| ≤
        |wMaskedOriginal M N Q β c a P| + |wMaskedZeroMode M N Q β c a P| +
          C * wMaskedTailEnvelope k M H N Q β c a P := by
  obtain ⟨C, hC, hb⟩ := wMaskedTail_uniform k
  refine ⟨C, hC, fun M hM H N Q β c a P hQ ↦ ?_⟩
  have he := wMaskedOriginal_eq_zero_add_truncated_add_tail hM H N Q β c a P hQ
  have ht : wMaskedTruncated M H N Q β c a P =
      (wMaskedOriginal M N Q β c a P - wMaskedZeroMode M N Q β c a P) -
        wMaskedTail M H N Q β c a P := by linarith
  rw [ht]
  exact (abs_sub _ _).trans
    (add_le_add (abs_sub _ _) (hb M hM H N Q β c a P hQ))

theorem wMaskedTruncated_eq_gcdMask
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WGCDData → Prop) (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q) :
    wMaskedTruncated M H N Q β c a (fun t ↦ P (wGCDTuple t)) =
      ∑ v ∈ (wGCDTuples N Q a).filter P, wGCDTerm M H β c a v := by
  unfold wMaskedTruncated wMaskedTuples
  rw [Finset.sum_filter, Finset.sum_filter, sum_wGCDTuples hN hQ]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs
  · exact (wGCDTerm_eq_originalTerm (wOriginalTuples_pos hN hQ ht)
      (Finset.mem_filter.mp ht).2 M H β c a).symm
  · rfl

/-- The exact large five-gcd contribution is a masked frequency sum. -/
theorem wGCDLargeSum_eq_maskedTruncated
    (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q) :
    wGCDLargeSum M Y H N Q β c a =
      wMaskedTruncated M H N Q β c a (fun t ↦ ¬(wGCDTuple t).Small Y) := by
  rw [wMaskedTruncated_eq_gcdMask M H N Q β c a (fun v ↦ ¬v.Small Y) hN hQ]
  unfold wGCDLargeSum
  apply Finset.sum_congr
  · ext v
    simp
  · intro v _
    rfl

theorem wGCDLargeSum_eq_original_sub_zero_sub_tail
    {M : ℝ} (hM : 0 < M) (Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ)
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q) :
    wGCDLargeSum M Y H N Q β c a =
      wMaskedOriginal M N Q β c a (fun t ↦ ¬(wGCDTuple t).Small Y) -
        wMaskedZeroMode M N Q β c a (fun t ↦ ¬(wGCDTuple t).Small Y) -
          wMaskedTail M H N Q β c a (fun t ↦ ¬(wGCDTuple t).Small Y) := by
  rw [wGCDLargeSum_eq_maskedTruncated M Y H N Q β c a hN hQ]
  have he := wMaskedOriginal_eq_zero_add_truncated_add_tail hM H N Q β c a
    (fun t ↦ ¬(wGCDTuple t).Small Y) (fun q hq ↦ (hQ q hq).ne')
  linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
