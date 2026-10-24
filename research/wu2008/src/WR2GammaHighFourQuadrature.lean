import WR2GammaHighFourClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSourceKQuadrature

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit FourPrimeContinuous HighBoxRecovery Real Finset Filter
open scoped Classical Topology

/-- Common threshold, actual phi, all high windows and original four words. -/
theorem high_K_uniform {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ d ∈ boxConvolutionSupport (windows j N), ∀ k : Fin 4,
        |sourceClosedK N d δ (Wu04RemainingCore.row j) k -
          sourceLegalK N d δ (Wu04RemainingCore.row j) k| < epsilon := by
  let Phi := max 2 (1 / (10*highEta))
  obtain ⟨R0, _, hR0⟩ := closedPrimeK_four_uniform Phi (le_max_left _ _) epsilon he
  have heta : 0 < 10*highEta := by norm_num [highEta]
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN j d hd
  let p := Wu04RemainingCore.row j
  have hp := (row_analytic j).mother
  have hs := (row_analytic j).two_lt_s.le
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := LowerTriple.phi_bounds j (by omega) hδ hδhi hd
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hgap : 0 < 2 * δ / (1/2-δ) := div_pos (by positivity) (by linarith)
    linarith [hg.2.2.1]
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hg.1
  have h := hR0 _ hlarge _ ⟨hphi, hg.2.2.2.trans (le_max_right _ _)⟩
    _ _ _ _ (sourceK_compact hp hs)
  simpa only [sourceClosedK, sourceLegalK, closedK, legalK, vec,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, Fin.cases_zero,
    Fin.cases_succ] using h

/-- Uniform quadrature paid at the reciprocal-mass scale. -/
theorem closedKMain_integral_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 4,
      closedKMain j N δ k ≤ integralKMain j N δ k +
        ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
  have hη : 0 < 10*highEta := by norm_num [highEta]
  obtain ⟨T,hT,h⟩ := high_K_uniform hd hh (mul_pos he hη)
  refine ⟨T,hT,?_⟩
  intro N hN j k
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have ht (d : ℕ) (hm : d ∈ boxConvolutionSupport (windows j N)) :
      (N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d)) * (ε*(10*highEta)) ≤ ε*((N:ℝ)/log N)/d := by
    have hp := LowerTriple.phi_bounds j (by omega : 2 ≤ N) hd hh hm
    have hg := log_le_log (rpow_pos_of_pos hn _) hp.1
    rw [log_rpow hn] at hg
    have hdp : (0:ℝ) < d := by
      exact_mod_cast (boxConvolutionSupport_pos (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hm)
    calc
      _ ≤ ((N:ℝ)/(d*((10*highEta)*log N))) * (ε*(10*highEta)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_pos he hη).le
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (mul_pos hdp (mul_pos hη hl))
          (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg d))
      _ = _ := by field_simp [show highEta ≠ 0 by norm_num [highEta]]
  unfold closedKMain integralKMain boxConvolutionReciprocalMass
  simp only [div_div]
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hm
  have hp := LowerTriple.phi_bounds j (by omega : 2 ≤ N) hd hh hm
  have ha := (abs_lt.mp (h N hN j d hm k)).2
  have hs : 0 ≤ (N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d)) :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (log_pos hp.2.1).le)
  have hb := mul_le_mul_of_nonneg_left (le_of_lt ha) hs
  have hc := ht d hm
  have hg := mul_le_mul_of_nonneg_left (hb.trans hc)
    (Nat.cast_nonneg (convolutionCoeff (windows j N) d))
  ring_nf at hg ⊢
  linarith only [hg]

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.closedKMain_integral_paid
