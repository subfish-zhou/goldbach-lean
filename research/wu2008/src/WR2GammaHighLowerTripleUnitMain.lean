import WR2GammaHighLowerTripleUnitPrefix
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitPrimeMain

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedUnit HighBoxRecovery Real Finset
open scoped Classical

def unitPrimeMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d,
      intervalMain (actualLower N δ (Wu04RemainingCore.row j) k d x) (actualUpper N δ (Wu04RemainingCore.row j) k d x)

/-- Full original sigma and pair support, without a nonunit feasibility gate. -/
def unitPrimeError (j : Fin 3) (N : ℕ) (η δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d, ((N : ℝ)/denominator d x)/(η*log N)

/-- Tau precedes the common threshold; all boxes, parameters and six bands follow it. -/
theorem unitMass_prime_main {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ k : Fin 6,
        unitMass j N δ k ≤ unitPrimeMain j N δ k +
          τ*unitPrimeError j N highEta δ k := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨T,hT,hscalar⟩ := interval_uniform_upper hη hτ
  refine ⟨T,hT,?_⟩
  intro N hN j k
  have hterm : ∀ d ∈ boxConvolutionSupport (windows j N),
      ∀ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d,
      prefixDifference (actualLower N δ (Wu04RemainingCore.row j) k d x) (actualUpper N δ (Wu04RemainingCore.row j) k d x) ≤
        intervalMain (actualLower N δ (Wu04RemainingCore.row j) k d x) (actualUpper N δ (Wu04RemainingCore.row j) k d x) +
        τ*(((N : ℝ)/denominator d x)/((highEta)*log N)) := by
    intro d hd x hx
    have hdp := boxConvolutionSupport_pos
      (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd
    have hD : 0 < denominator d x := denominator_pos hdp hx
    have hq := (window_lower j (by omega : 2 ≤ N) hδ hδhi hd
      (mem_pairs.mp hx).2.1).2
    apply hscalar N hN
    · exact hq.trans (le_max_left _ _)
    · exact min_le_right _ _
    · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hD.le)
  rw [unitMass_pair_prefix]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport (windows j N),
        (convolutionCoeff (windows j N) d : ℝ) *
        ∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d,
          (intervalMain (actualLower N δ (Wu04RemainingCore.row j) k d x) (actualUpper N δ (Wu04RemainingCore.row j) k d x) +
            τ*(((N : ℝ)/denominator d x)/((highEta)*log N))) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (sum_le_sum (hterm d hd)) (Nat.cast_nonneg _)
    _ = _ := by
      unfold unitPrimeMain unitPrimeError
      simp only [sum_add_distrib,← mul_sum,mul_add,mul_left_comm]


end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.unitMass_prime_main
