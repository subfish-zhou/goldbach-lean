import WR2GammaHighLowerTripleClosedK

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleContinuous HighBoxRecovery Real Finset Filter
open scoped Classical Topology

/-- One threshold for the actual phi and all three high windows and six bands. -/
theorem high_K_uniform {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ d ∈ boxConvolutionSupport (windows j N), ∀ k : Fin 6,
        let p := Wu04RemainingCore.row j
        |closedPrimeKj ((N:ℝ)^(1/2-δ)/d) (1/p.S) (1/p.kappa1)
          (1/p.kappa2) (1/p.kappa3) (1/p.s) k (omega3XPhi N d δ) -
          K (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) k
            (omega3XPhi N d δ)| < ε := by
  obtain ⟨R0,_,hR0⟩ := closedPrimeK_six_uniform (1/(10*highEta))
    (by norm_num [highEta]) ε he
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num [highEta] : 0 < 10*highEta)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN j d hm k
  have hp := phi_bounds j (by omega : 2 ≤ N) hd hh hm
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hnonneg : 0 ≤ 2*δ/(1/2-δ) := div_nonneg (by positivity) (by linarith)
    linarith [hp.2.2.1]
  exact hR0 _ ((hT N (by omega)).trans hp.1) _ ⟨hphi,hp.2.2.2⟩
    _ _ _ _ _ (mother_compact_parameters _ (row_analytic j).mother
      (row_analytic j).two_lt_s.le) k

/-- Original convolution weights and the actual varying phi are retained. -/
def closedKMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  let p := Wu04RemainingCore.row j
  ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
    ((N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d))) *
      closedPrimeKj ((N:ℝ)^(1/2-δ)/d) (1/p.S) (1/p.kappa1) (1/p.kappa2)
        (1/p.kappa3) (1/p.s) k (omega3XPhi N d δ)

def integralKMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  let p := Wu04RemainingCore.row j
  ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
    ((N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d))) *
      K (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) k (omega3XPhi N d δ)

/-- Uniform quadrature paid at the reciprocal-mass scale. -/
theorem closedKMain_integral_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 6,
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
    have hp := phi_bounds j (by omega : 2 ≤ N) hd hh hm
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
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hm
  have hp := phi_bounds j (by omega : 2 ≤ N) hd hh hm
  have ha := (abs_lt.mp (h N hN j d hm k)).2
  have hs : 0 ≤ (N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d)) :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (log_pos hp.2.1).le)
  have hb := mul_le_mul_of_nonneg_left (le_of_lt ha) hs
  have hc := ht d hm
  have hg := mul_le_mul_of_nonneg_left (hb.trans hc)
    (Nat.cast_nonneg (convolutionCoeff (windows j N) d))
  ring_nf at hg ⊢
  linarith only [hg]

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.closedKMain_integral_paid
