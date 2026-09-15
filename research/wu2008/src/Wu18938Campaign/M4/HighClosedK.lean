import Wu18938Campaign.M4.HighFiniteError
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteToClosedK
import WR2PsiCostsWellposed

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real Filter
open LiLiuPrereqBuchstab HighBoxRecovery MeasureTheory SecondFunctionalJointTail
open scoped Classical

def originalHighCost (j : Fin 3) (high : Bool) : ℝ :=
  if high then WuPaper.R2PsiCosts.I21 (Wu04RemainingCore.row j)
  else WuPaper.R2PsiCosts.I20 (Wu04RemainingCore.row j)

theorem original_high_cost_nonneg (j : Fin 3) (high : Bool) :
    0 ≤ originalHighCost j high := by
  have h := WuPaper.R2PsiCosts.originalI_nonnegative (Wu04RemainingCore.row j)
    (row_analytic j).mother (row_analytic j).two_lt_s.le
  cases high
  · exact h.2.2.2.1
  · exact h.2.2.2.2

theorem original_legalK_le_cost {N d : ℕ} {δ : ℝ} (j : Fin 3) (high : Bool)
    (hphi : 2 ≤ omega3XPhi N d δ) :
    sourceLegalK N d δ (Wu04RemainingCore.row j) high ≤ originalHighCost j high := by
  let p := Wu04RemainingCore.row j
  have hp := (row_analytic j).mother
  have hs := (row_analytic j).two_lt_s.le
  cases high
  · have hm : 0 ≤ WuPaper.R2PsiCosts.missingMass 3 (WuPaper.R2PsiCosts.D20 p)
        (omega3XPhi N d δ) := by
      apply setIntegral_nonneg ((WuPaper.R2PsiCosts.D20_measurable p).diff
        (HighNonunitLegal.legal_measurable _ _))
      intro t ht
      exact geometricWeight_nonneg _ (WuPaper.R2PsiCosts.D20_cube p hp hs ht.1)
    have he := WuPaper.R2PsiCosts.K20_split p hp hs (omega3XPhi N d δ)
    have hb := WuPaper.R2PsiCosts.le_phiSup (WuPaper.R2PsiCosts.K20_bdd p hp hs) hphi
    change HighNonunitLegal.K20 _ _ _ _ ≤ WuPaper.R2PsiCosts.I20 p
    change WuPaper.R2PsiCosts.K20 p (omega3XPhi N d δ) ≤ WuPaper.R2PsiCosts.I20 p at hb
    linarith only [hm, he, hb]
  · have hm : 0 ≤ WuPaper.R2PsiCosts.missingMass 4 (WuPaper.R2PsiCosts.D21 p)
        (omega3XPhi N d δ) := by
      apply setIntegral_nonneg ((WuPaper.R2PsiCosts.D21_measurable p).diff
        (HighNonunitLegal.legal_measurable _ _))
      intro t ht
      exact geometricWeight_nonneg _ (WuPaper.R2PsiCosts.D21_cube p hp hs ht.1)
    have he := WuPaper.R2PsiCosts.K21_split p hp hs (omega3XPhi N d δ)
    have hb := WuPaper.R2PsiCosts.le_phiSup (WuPaper.R2PsiCosts.K21_bdd p hp hs) hphi
    change HighNonunitLegal.K21 _ _ _ ≤ WuPaper.R2PsiCosts.I21 p
    change WuPaper.R2PsiCosts.K21 p (omega3XPhi N d δ) ≤ WuPaper.R2PsiCosts.I21 p at hb
    linarith only [hm, he, hb]

theorem original_finite_inner_closed {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool)
    (hdm : d ∈ boxConvolutionSupport (windows j N)) :
    (∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) high d,
      buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) *
        ((N : ℝ) / tupleProduct d t) / log t.2.1) ≤
      ((N : ℝ) / d / log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        sourceClosedK N d δ (Wu04RemainingCore.row j) high := by
  have hdw : d ∈ WuSource.SrcSingle.psiPrimes (j.castAdd 4) N := by
    simpa only [support_eq] using hdm
  have hd0 := (mem_primeWindow.mp hdw).1.pos
  have hR := (prime_geometry j (by omega) hd hh hdw).2.2.2.2.2.2.2
  let S := legalPrimeTuples N δ (Wu04RemainingCore.row j) high d
  have hlen : ∀ t ∈ S, (tupleList t).length = if high then 6 else 5 :=
    fun t ht => high_tuple_length high (mem_filter.mp ht).1
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    fun t ht => original_tuple_cube j (by omega) hd hh hdm (mem_filter.mp ht).1
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have h := tupleProduct_pos hd0 (mem_filter.mp t.property).1
    by_contra hz
    have he := Nat.eq_zero_of_not_pos hz
    simp only [tupleProduct, he, mul_zero, lt_self_iff_false] at h
  have hprime (t : S) : 1 < t.val.2.1 :=
    (mem_primeWindow.mp (mem_primeTuples.mp (mem_filter.mp t.property).1).2.1).1.one_lt
  have hgate (t : S) : tupleProduct d t.val * t.val.2.1 ≤ N := (mem_filter.mp t.property).2
  have hscale : 0 ≤ (N : ℝ) / d / log ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    div_nonneg (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)) (log_pos hR).le
  cases high with
  | false =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 3) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * HighNonunitLegal.closedPrimeK20 _ _ _ _ _
    rw [finiteTransport_closed20]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 3
    · intro t
      exact tuple_embedding_D20 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2
  | true =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 4) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * HighNonunitLegal.closedPrimeK21 _ _ _ _
    rw [finiteTransport_closed21]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 4
    · intro t
      exact tuple_embedding_D21 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2

theorem original_closedK_le_cost {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ high : Bool, ∀ d ∈ boxConvolutionSupport (windows j N),
      sourceClosedK N d δ (Wu04RemainingCore.row j) high ≤ originalHighCost j high + ε := by
  let Phi : ℝ := 1 / (10 * highEta)
  have hPhi : 2 ≤ Phi := by norm_num [Phi, highEta]
  obtain ⟨R0, _, h0⟩ := HighNonunitLegal.closedPrimeK20_uniform Phi hPhi ε heps
  obtain ⟨R1, _, h1⟩ := HighNonunitLegal.closedPrimeK21_uniform Phi hPhi ε heps
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num [highEta] : (0 : ℝ) < 10 * highEta)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (max R0 R1)))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro δ hd hh N hN j high d hdm
  have hdw : d ∈ WuSource.SrcSingle.psiPrimes (j.castAdd 4) N := by
    simpa only [support_eq] using hdm
  have hg := HighO3.phi_bounds (by omega : 2 ≤ N) (mem_primeWindow.mp hdw).1.pos hd
    (show δ < 1 / 2 by linarith) (by norm_num [highEta] : 0 < highEta)
    (support_size j (by omega) hd hh d hdm)
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hden : 0 < 1 / 2 - δ := by linarith
    have hgap : 0 ≤ 2 * δ / (1 / 2 - δ) := by positivity
    linarith [hg.2.2.1]
  have hlarge := (hT N (by omega)).trans hg.1
  obtain ⟨ha, h23, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds
    (row_analytic j).mother (row_analytic j).two_lt_s.le
  have hclose : |sourceClosedK N d δ (Wu04RemainingCore.row j) high -
      sourceLegalK N d δ (Wu04RemainingCore.row j) high| < ε := by
    cases high
    · exact h0 _ ((le_max_left _ _).trans hlarge) _ ⟨hphi, hg.2.2.2⟩ _ _ _ ha hb
    · exact h1 _ ((le_max_right _ _).trans hlarge) _ ⟨hphi, hg.2.2.2⟩ _ _ (ha.trans h23) hb
  have hc := original_legalK_le_cost j high hphi
  linarith only [(abs_lt.mp hclose).2, hc]

end Wu18938Campaign.M4
