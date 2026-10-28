import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramAggregateBound

/-!
# The nonzero secondary resonance with a common first beta index

The relation `h'*s = h*s'` does not force the correlation numerator to
vanish. In this branch its common `n*s'` factor is extracted before
averaging in `r`, never by applying a nonzero-coefficient mean in `n`.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def iv3SecondaryNumerator (d₁ n₂ n₂' : ℕ) (a h : ℤ) : ℤ :=
  a * d₁ * h * ((n₂' : ℤ) - n₂)

theorem iv3CorrelationNumerator_secondary
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s') :
    iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' =
      (n * s' : ℕ) * iv3SecondaryNumerator d₁ n₂ n₂' a h := by
  unfold iv3CorrelationNumerator iv3SecondaryNumerator
  push_cast
  calc
    _ = a * ((h * s') * n₂' * ((d₁ : ℤ) * n - n₂) -
        (h' * s) * n₂ * ((d₁ : ℤ) * n - n₂')) := by ring
    _ = _ := by rw [hsec]; ring

theorem iv3SecondaryNumerator_ne_zero
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) :
    iv3SecondaryNumerator d₁ n₂ n₂' a h ≠ 0 := by
  rw [iv3CorrelationNumerator_secondary hsec] at hl
  exact (mul_ne_zero_iff.mp hl).2

theorem iv3_secondary_gcd
    {d₁ n n₂ n₂' r s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s') :
    (n * r * s * s').gcd
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs =
      (n * s') * (r * s).gcd (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs := by
  rw [iv3CorrelationNumerator_secondary hsec, Int.natAbs_mul, Int.natAbs_natCast,
    show n * r * s * s' = (n * s') * (r * s) by ring, Nat.gcd_mul_left]


/-- The secondary branch is not excluded by the nonzero numerator filter. -/
def wGramSecondaryResonant (L : WGramLabel) : Prop :=
  L.2.2.2.2 * L.2.1.2.1 = L.2.1.2.2 * L.2.2.2.1

theorem sum_wGram_nonzero_split_secondary
    (G : Finset WGramLabel) (K : WExtractedKey) (a : ℤ) (F : WGramLabel → ℝ) :
    (∑ L ∈ G.filter (fun L => wGramNumerator K a L ≠ 0), F L) =
      (∑ L ∈ G.filter (fun L =>
        wGramNumerator K a L ≠ 0 ∧ wGramSecondaryResonant L), F L) +
      ∑ L ∈ G.filter (fun L =>
        wGramNumerator K a L ≠ 0 ∧ ¬ wGramSecondaryResonant L), F L := by
  simpa only [filter_filter] using
    (sum_filter_add_sum_filter_not
      (G.filter (fun L => wGramNumerator K a L ≠ 0)) wGramSecondaryResonant F).symm


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
