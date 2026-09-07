import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDelayedFactorExtraction
import Mathlib.Data.Nat.Log

/-!
# Disjoint dyadic pieces of the retained frequencies

The half-open shells avoid duplicating powers of two. Both signs stay in
the same shell, and zero is removed using its actual zero summand.
The original tuple-dependent cutoff is retained, not enlarged.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def frequencyBlock {ι : Type*} (T : Finset ι) (h : ι → ℤ) (j : ℕ) : Finset ι :=
  T.filter (fun t => h t ≠ 0 ∧ Nat.log 2 (h t).natAbs = j)

theorem mem_frequencyBlock_iff {ι : Type*} {T : Finset ι} {h : ι → ℤ}
    {j : ℕ} {t : ι} :
    t ∈ frequencyBlock T h j ↔
      t ∈ T ∧ 2 ^ j ≤ (h t).natAbs ∧ (h t).natAbs < 2 ^ (j + 1) := by
  simp only [frequencyBlock, mem_filter]
  constructor
  · rintro ⟨ht, hne, rfl⟩
    exact ⟨ht, Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.mpr hne),
      Nat.lt_pow_succ_log_self (by decide) _⟩
  · rintro ⟨ht, hlo, hhi⟩
    have hn : (h t).natAbs ≠ 0 :=
      (lt_of_lt_of_le (by positivity : 0 < 2 ^ j) hlo).ne'
    exact ⟨ht, Int.natAbs_ne_zero.mp hn,
      (Nat.log_eq_iff (Or.inr ⟨by decide, hn⟩)).mpr ⟨hlo, hhi⟩⟩

theorem sum_eq_frequencyBlocks {ι A : Type*} [AddCommMonoid A]
    (T : Finset ι) (h : ι → ℤ) (F : ι → A) (B : ℕ)
    (hB : ∀ t ∈ T, (h t).natAbs ≤ B)
    (hzero : ∀ t ∈ T, h t = 0 → F t = 0) :
    ∑ t ∈ T, F t =
      ∑ j ∈ range (Nat.log 2 B + 1), ∑ t ∈ frequencyBlock T h j, F t := by
  have he : ∑ t ∈ T.filter (fun t => h t ≠ 0), F t = ∑ t ∈ T, F t :=
    sum_filter_of_ne (fun t ht hne hz => hne (hzero t ht hz))
  rw [← he]
  symm
  convert sum_fiberwise_of_maps_to
    (s := T.filter (fun t => h t ≠ 0))
    (t := range (Nat.log 2 B + 1)) (g := fun t => Nat.log 2 (h t).natAbs)
    (fun t ht => mem_range.mpr (Nat.lt_succ_of_le
      (Nat.log_mono_right (hB t (mem_filter.mp ht).1)))) F using 1
  apply sum_congr rfl
  intro j _
  congr 1
  ext t
  simp [frequencyBlock, and_assoc]

/-- A genuine logarithmic-loss reduction: the chosen shell is a maximum
of the actual complex shell sums, not a bound supplied by the caller. -/
theorem exists_frequencyBlock_norm_bound {ι : Type*}
    (T : Finset ι) (h : ι → ℤ) (F : ι → ℂ) (B : ℕ)
    (hB : ∀ t ∈ T, (h t).natAbs ≤ B)
    (hzero : ∀ t ∈ T, h t = 0 → F t = 0) :
    ∃ j ≤ Nat.log 2 B, ‖∑ t ∈ T, F t‖ ≤
      (Nat.log 2 B + 1 : ℕ) * ‖∑ t ∈ frequencyBlock T h j, F t‖ := by
  obtain ⟨j, hj, hmax⟩ := exists_max_image (range (Nat.log 2 B + 1))
    (fun j => ‖∑ t ∈ frequencyBlock T h j, F t‖)
    ⟨0, mem_range.mpr (by omega)⟩
  refine ⟨j, by simpa using hj, ?_⟩
  rw [sum_eq_frequencyBlocks T h F B hB hzero]
  exact (norm_sum_le _ _).trans (by
    simpa only [card_range, nsmul_eq_mul] using
      sum_le_card_nsmul (range (Nat.log 2 B + 1))
        (fun j => ‖∑ t ∈ frequencyBlock T h j, F t‖)
        ‖∑ t ∈ frequencyBlock T h j, F t‖ hmax)

abbrev WExtractedTuple := FactorExtractionTuple × (ℕ × (ℕ × ℕ))

def wExtractedOriginal (z : WExtractedTuple) : WOriginalTuple :=
  ((z.2.1, (z.1.1.1 * z.1.2.1) * (z.1.1.2 * z.1.2.2)), z.2.2)

def wExtractedCoefficient (β c₁ γ ζ : ℕ → ℝ) (z : WExtractedTuple) : ℝ :=
  γ (z.1.1.1 * z.1.2.1) * ζ (z.1.1.2 * z.1.2.2) *
    (c₁ z.2.1 * β z.2.2.1 * β z.2.2.2)

def wExtractedFrequencies (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    Finset (WExtractedTuple × ℤ) :=
  (wFactorExtractionTuples N Q a P R S ξ).biUnion (fun z =>
    ({z} : Finset WExtractedTuple) ×ˢ
      Icc (-(H (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2 : ℤ))
        (H (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2))

theorem mem_wExtractedFrequencies_iff {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ}
    {t : WExtractedTuple × ℤ} :
    t ∈ wExtractedFrequencies H N Q a P R S ξ ↔
      t.1 ∈ wFactorExtractionTuples N Q a P R S ξ ∧
      -(H (wExtractedOriginal t.1).1.1 (wExtractedOriginal t.1).1.2 : ℤ) ≤ t.2 ∧
      t.2 ≤ H (wExtractedOriginal t.1).1.1 (wExtractedOriginal t.1).1.2 := by
  simp only [wExtractedFrequencies, mem_biUnion, mem_product, mem_singleton, mem_Icc]
  constructor
  · rintro ⟨z, hz, he, hh⟩
    exact he ▸ ⟨hz, hh⟩
  · rintro ⟨hz, hh⟩
    exact ⟨t.1, hz, rfl, hh⟩

def wExtractedFrequencyTerm (M : ℝ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (t : WExtractedTuple × ℤ) : ℂ :=
  (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
    wPoissonFrequency M a (wExtractedOriginal t.1).1.1
      (wExtractedOriginal t.1).1.2 (wExtractedOriginal t.1).2.1
      (wExtractedOriginal t.1).2.2 t.2

theorem wExtractedFrequencyTerm_zero (M : ℝ) (β c₁ γ ζ : ℕ → ℝ)
    (a : ℤ) (z : WExtractedTuple) :
    wExtractedFrequencyTerm M β c₁ γ ζ a (z, 0) = 0 := by
  simp [wExtractedFrequencyTerm, wPoissonFrequency, dyadicCutoffPoissonRemainder]

theorem wMaskedFactorExtractedTruncated_eq_frequencies
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    wMaskedFactorExtractedTruncated M H N Q β c₁ γ ζ a P R S ξ =
      (∑ t ∈ wExtractedFrequencies H N Q a P R S ξ,
        wExtractedFrequencyTerm M β c₁ γ ζ a t).re := by
  have hd : (wFactorExtractionTuples N Q a P R S ξ : Set WExtractedTuple).Pairwise
      (fun z u => Disjoint
        (({z} : Finset WExtractedTuple) ×ˢ
          Icc (-(H (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2 : ℤ))
            (H (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2))
        (({u} : Finset WExtractedTuple) ×ˢ
          Icc (-(H (wExtractedOriginal u).1.1 (wExtractedOriginal u).1.2 : ℤ))
            (H (wExtractedOriginal u).1.1 (wExtractedOriginal u).1.2))) := by
    intro z _ u _ hne
    apply disjoint_left.mpr
    intro t ht hu
    exact hne ((mem_singleton.mp (mem_product.mp ht).1).symm.trans
      (mem_singleton.mp (mem_product.mp hu).1))
  rw [wExtractedFrequencies, sum_biUnion hd]
  simp only [sum_product, sum_singleton, Complex.re_sum]
  unfold wMaskedFactorExtractedTruncated wSecondModulusKernel
  apply sum_congr rfl
  intro z _
  simp only [wExtractedFrequencyTerm, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← mul_sum, wExtractedCoefficient,
    wExtractedOriginal, Complex.re_sum]
  ring

/-- This maximum only bounds the already retained frequency sets. The
individual cutoffs remain tests in `wExtractedFrequencies`. -/
def wExtractedMaxFrequency (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) : ℕ :=
  (wFactorExtractionTuples N Q a P R S ξ).sup
    (fun z => H (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2)

theorem wExtractedFrequencies_natAbs_le {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedFrequencies H N Q a P R S ξ) :
    t.2.natAbs ≤ wExtractedMaxFrequency H N Q a P R S ξ := by
  obtain ⟨hz, hlo, hhi⟩ := mem_wExtractedFrequencies_iff.mp ht
  have hh : (t.2.natAbs : ℤ) ≤
      H (wExtractedOriginal t.1).1.1 (wExtractedOriginal t.1).1.2 := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr ⟨hlo, hhi⟩
  have hn : t.2.natAbs ≤
      H (wExtractedOriginal t.1).1.1 (wExtractedOriginal t.1).1.2 := by
    exact_mod_cast hh
  exact hn.trans (le_sup (f := fun z =>
    H (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2) hz)

/-- The actual signed extracted W is controlled by one actual dyadic
Fourier piece, with an explicit logarithmic number of pieces. -/
theorem wMaskedFactorExtractedTruncated_dyadic_bound
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    ∃ j ≤ Nat.log 2 (wExtractedMaxFrequency H N Q a P R S ξ),
      |wMaskedFactorExtractedTruncated M H N Q β c₁ γ ζ a P R S ξ| ≤
        (Nat.log 2 (wExtractedMaxFrequency H N Q a P R S ξ) + 1 : ℕ) *
          ‖∑ t ∈ frequencyBlock (wExtractedFrequencies H N Q a P R S ξ) Prod.snd j,
            wExtractedFrequencyTerm M β c₁ γ ζ a t‖ := by
  obtain ⟨j, hj, hb⟩ := exists_frequencyBlock_norm_bound
    (wExtractedFrequencies H N Q a P R S ξ) Prod.snd
    (wExtractedFrequencyTerm M β c₁ γ ζ a)
    (wExtractedMaxFrequency H N Q a P R S ξ)
    (fun _ ht => wExtractedFrequencies_natAbs_le ht)
    (fun t _ ht => by
      rcases t with ⟨z, h⟩
      dsimp only at ht
      subst h
      exact wExtractedFrequencyTerm_zero M β c₁ γ ζ a z)
  refine ⟨j, hj, ?_⟩
  rw [wMaskedFactorExtractedTruncated_eq_frequencies]
  exact (Complex.abs_re_le_norm _).trans hb

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
