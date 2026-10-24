import WR2GammaHighTailFinitePaid
import WR2GammaHighLowerTripleClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteToClosedK

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighNonunitLegal HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

def closedKMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
    ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d)) * sourceClosedK N d δ (Wu04RemainingCore.row j) k

def integralKMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
    ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d)) * sourceLegalK N d δ (Wu04RemainingCore.row j) k

theorem finite_inner_le_sourceClosedK {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (high : Bool)
    (hd : d ∈ boxConvolutionSupport (windows j N)) :
    (∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) high d,
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1) ≤
      ((N : ℝ)/d/log ((N : ℝ)^(1/2-δ)/d)) * sourceClosedK N d δ (Wu04RemainingCore.row j) high := by
  have hd0 : 0 < d := boxConvolutionSupport_pos
    (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hd
  have hR := (LowerTriple.phi_bounds j (by omega) hδ hδhi hd).2.1
  let S := legalPrimeTuples N δ (Wu04RemainingCore.row j) high d
  have hlen : ∀ t ∈ S, (tupleList t).length = if high then 6 else 5 :=
    fun t ht => high_tuple_length high (mem_filter.mp ht).1
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d) :=
    fun t ht => actual_tuple_cube j (by omega) hδ hδhi hd (mem_filter.mp ht).1
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have hh := tupleProduct_pos hd0 (mem_filter.mp t.property).1
    by_contra hz
    have he := Nat.eq_zero_of_not_pos hz
    simp only [tupleProduct, he, mul_zero, lt_self_iff_false] at hh
  have hprime (t : S) : 1 < t.val.2.1 :=
    (mem_primeWindow.mp (mem_primeTuples.mp (mem_filter.mp t.property).1).2.1).1.one_lt
  have hgate (t : S) : tupleProduct d t.val * t.val.2.1 ≤ N := (mem_filter.mp t.property).2
  have hscale : 0 ≤ (N : ℝ)/d/log ((N : ℝ)^(1/2-δ)/d) :=
    div_nonneg (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)) (log_pos hR).le
  cases high with
  | false =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 3) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * closedPrimeK20 _ _ _ _ _
    rw [finiteTransport_closed20]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 3
    · intro t
      exact tuple_embedding_D20 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2
  | true =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 4) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * closedPrimeK21 _ _ _ _
    rw [finiteTransport_closed21]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 4
    · intro t
      exact tuple_embedding_D21 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2

/-- Original sigma and all ordered labels, with the actual scale paid exactly once. -/
theorem finiteBuchstabMain_le_sourceClosedKMass {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Bool) :
    finiteBuchstabMain j N δ k ≤ closedKMain j N δ k := by
  unfold finiteBuchstabMain closedKMain
  apply sum_le_sum
  intro d hd
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (finite_inner_le_sourceClosedK j hN hδ hδhi k hd)
    (Nat.cast_nonneg (convolutionCoeff (windows j N) d))

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.finiteBuchstabMain_le_sourceClosedKMass
