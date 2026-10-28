import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWGCD

/-!
# Exact five-gcd reindexing of the retained W sum

All finite supports, signed coefficients, and frequencies are preserved.
The large-factor contribution is split off explicitly, not declared negligible.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WOriginalTuple := (ℕ × ℕ) × (ℕ × ℕ)

def WGCDData.original (v : WGCDData) : WOriginalTuple :=
  ((v.δ * v.δ₁ * v.k₁, v.δ * v.δ₂ * v.k₂),
    (v.d * v.d₁ * v.n₁, v.d * v.n₂))

def wGCDTuple (t : WOriginalTuple) : WGCDData :=
  wGCDData t.1.1 t.1.2 t.2.1 t.2.2


def wOriginalTuples (N Q : Finset ℕ) (a : ℤ) : Finset WOriginalTuple :=
  ((reducedModuli Q a ×ˢ reducedModuli Q a) ×ˢ (N ×ˢ N)).filter
    (fun t ↦ WCompatible t.1.1 t.1.2 t.2.1 t.2.2)


def wOriginalTerm (M : ℝ) (H : ℕ → ℕ → ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (t : WOriginalTuple) : ℝ :=
  (c t.1.1 * c t.1.2 * β t.2.1 * β t.2.2) *
    (∑ h ∈ Finset.Icc (-(H t.1.1 t.1.2 : ℤ)) (H t.1.1 t.1.2),
      wPoissonFrequency M a t.1.1 t.1.2 t.2.1 t.2.2 h).re

theorem truncatedWNonzeroMode_eq_originalTuples
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    truncatedWNonzeroMode M H N Q β c a =
      ∑ t ∈ wOriginalTuples N Q a, wOriginalTerm M H β c a t := by
  simp only [wOriginalTuples, Finset.sum_filter, Finset.sum_product,
    truncatedWNonzeroMode, wOriginalTerm]


def WGCDData.key (v : WGCDData) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (v.d, v.d₁, v.δ, v.δ₁, v.δ₂)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
