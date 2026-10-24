import WR2GammaHighLowerTripleFiniteDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteToClosedK

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

/-- Actual high-window phi has a fixed compact range. -/
theorem phi_bounds {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : d ∈ boxConvolutionSupport (windows j N)) :
    (N:ℝ)^(10*highEta) ≤ (N:ℝ)^(1/2-δ)/d ∧
    1 < (N:ℝ)^(1/2-δ)/d ∧
    2+2*δ/(1/2-δ) ≤ omega3XPhi N d δ ∧
    omega3XPhi N d δ ≤ 1/(10*highEta) := by
  have hd' := hd
  rw [support_eq] at hd'
  have hg := prime_geometry j hN hδ hδhi hd'
  have hd0 := hg.1.one_le
  have hR := hg.2.2.2.2.2.2.1
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hdpos : (0 : ℝ) < d := by linarith
  have hη : 0 < 10*highEta := by norm_num [highEta]
  have hc : 0 < 1 / 2 - δ := by linarith
  have hR1 := (one_lt_rpow hN1 hη).trans_le hR
  have hL : 0 < log ((N : ℝ) ^ (1 / 2 - δ) / d) := log_pos hR1
  have hlogR :
      log ((N : ℝ) ^ (1 / 2 - δ) / d) =
        (1 / 2 - δ) * log N - log d := by
    rw [log_div (rpow_pos_of_pos hN0 _).ne' hdpos.ne', log_rpow hN0]
  have hlogNd : log ((N : ℝ) / d) = log N - log d :=
    log_div hN0.ne' hdpos.ne'
  have hlogd : 0 ≤ log (d : ℝ) := log_nonneg hd1
  have hloglower := log_le_log (rpow_pos_of_pos hN0 _) hR
  rw [log_rpow hN0] at hloglower
  refine ⟨hR, hR1, ?_, ?_⟩
  · have heq : 2 + 2 * δ / (1 / 2 - δ) = 1 / (1 / 2 - δ) := by
      apply (eq_div_iff hc.ne').mpr
      rw [add_mul, div_mul_cancel₀ _ hc.ne']
      ring
    rw [heq, omega3XPhi, le_div_iff₀ hL, one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ hc).mpr
    rw [hlogR, hlogNd]
    nlinarith
  · rw [omega3XPhi, div_le_iff₀ hL, one_div, ← div_eq_inv_mul]
    apply (le_div_iff₀ hη).mpr
    rw [hlogNd]
    nlinarith

theorem filtered_inner_le_closedPrimeKj {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Fin 6)
    (hd : d ∈ boxConvolutionSupport (windows j N)) :
    (∑ t ∈ (legalPrimeTriples N δ (Wu04RemainingCore.row j) k d).filter
      (fun t => (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1 ≤ (t.2.2 : ℝ)),
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1) ≤
    ((N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d))) *
      LowerTripleContinuous.closedPrimeKj ((N : ℝ)^(1/2-δ)/d)
        (1/(Wu04RemainingCore.row j).S) (1/(Wu04RemainingCore.row j).kappa1) (1/(Wu04RemainingCore.row j).kappa2) (1/(Wu04RemainingCore.row j).kappa3) (1/(Wu04RemainingCore.row j).s) k (omega3XPhi N d δ) := by
  have hd0 : 0 < d := boxConvolutionSupport_pos
    (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hd
  have hbds := phi_bounds j (by omega) hδ hδhi hd
  have hR := hbds.2.1
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hpos : 0 ≤ 2*δ/(1/2-δ) := div_nonneg (by positivity) (by linarith)
    linarith [hbds.2.2.1]
  let S := (legalPrimeTriples N δ (Wu04RemainingCore.row j) k d).filter
    (fun t => (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1 ≤ (t.2.2 : ℝ))
  have hactual (t : S) : t.val ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d :=
    (mem_filter.mp (mem_filter.mp t.property).1).1
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d) :=
    fun t ht => actual_tuple_cube j (by omega) hδ hδhi hd (hactual ⟨t,ht⟩)
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have hh := tupleProduct_pos hd0 (hactual t)
    rw [tupleProduct_literal] at hh
    by_contra hn
    have he := Nat.eq_zero_of_not_pos hn
    simp only [he, mul_zero, lt_self_iff_false] at hh
  have hprime (t : S) : 1 < t.val.2.1 :=
    (mem_primeWindow.mp (mem_primeTriples.mp (hactual t)).2.1).1.one_lt
  have hscale : 0 ≤ (N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d)) :=
    div_nonneg (Nat.cast_nonneg N) (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)
  unfold LowerTripleContinuous.closedPrimeKj
  rw [closedPrimeK_sum]
  apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hmem) 1
  · intro t
    exact tuple_embedding_closed_domain hR S hmem t k (hactual t) (mem_filter.mp t.property).2
  · intro t
    exact tupleCubeEmbedding_kernel (by omega) hd0 hR hphi S hmem t (hprod t) (hprime t)

/-- The full original sigma is retained, with no transport or mask hypothesis. -/
theorem filtered_finiteBuchstabMain_le_closedPrimeKj {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Fin 6) :
    (∑ d ∈ boxConvolutionSupport (windows j N),
      (convolutionCoeff (windows j N) d : ℝ) * (∑ t ∈ (legalPrimeTriples N δ (Wu04RemainingCore.row j) k d).filter
      (fun t => (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1 ≤ (t.2.2 : ℝ)),
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1)) ≤
    ∑ d ∈ boxConvolutionSupport (windows j N),
      (convolutionCoeff (windows j N) d : ℝ) * ((N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d))) *
      LowerTripleContinuous.closedPrimeKj ((N : ℝ)^(1/2-δ)/d)
        (1/(Wu04RemainingCore.row j).S) (1/(Wu04RemainingCore.row j).kappa1) (1/(Wu04RemainingCore.row j).kappa2) (1/(Wu04RemainingCore.row j).kappa3) (1/(Wu04RemainingCore.row j).s) k (omega3XPhi N d δ) := by
  apply sum_le_sum
  intro d hd
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (filtered_inner_le_closedPrimeKj j hN hδ hδhi k hd)
    (Nat.cast_nonneg (convolutionCoeff (windows j N) d))

/-- All six independent closed atoms, without union or product-image deduplication. -/
theorem filtered_finiteBuchstabMain_all6_le_closedPrimeKj {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (∑ k : Fin 6, ∑ d ∈ boxConvolutionSupport (windows j N),
      (convolutionCoeff (windows j N) d : ℝ) * (∑ t ∈ (legalPrimeTriples N δ (Wu04RemainingCore.row j) k d).filter
      (fun t => (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1 ≤ (t.2.2 : ℝ)),
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1)) ≤
    ∑ k : Fin 6, ∑ d ∈ boxConvolutionSupport (windows j N),
      (convolutionCoeff (windows j N) d : ℝ) * ((N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d))) *
      LowerTripleContinuous.closedPrimeKj ((N : ℝ)^(1/2-δ)/d)
        (1/(Wu04RemainingCore.row j).S) (1/(Wu04RemainingCore.row j).kappa1) (1/(Wu04RemainingCore.row j).kappa2) (1/(Wu04RemainingCore.row j).kappa3) (1/(Wu04RemainingCore.row j).s) k (omega3XPhi N d δ) := by
  exact sum_le_sum (fun k _ => filtered_finiteBuchstabMain_le_closedPrimeKj j hN hδ hδhi k)

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.filtered_finiteBuchstabMain_all6_le_closedPrimeKj
