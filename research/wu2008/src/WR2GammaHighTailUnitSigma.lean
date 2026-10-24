import WR2GammaHighTailUnitSource

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnit HighUnitSource HighBoxRecovery Real Finset
open scoped Classical

theorem log_scale_error_le {N d : ℕ} {δ ε : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hm : d ∈ boxConvolutionSupport (windows j N)) (he : 0 ≤ ε) :
    (N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d)) * (ε*(10*highEta)) ≤ ε*((N:ℝ)/log N)/d := by
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hη : 0 < 10*highEta := by norm_num [highEta]
  have hp := LowerTriple.phi_bounds j hN hd hh hm
  have hg := log_le_log (rpow_pos_of_pos hn _) hp.1
  rw [log_rpow hn] at hg
  have hdp : (0:ℝ) < d := by
    exact_mod_cast (boxConvolutionSupport_pos (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hm)
  calc
    _ ≤ ((N:ℝ)/(d*((10*highEta)*log N))) * (ε*(10*highEta)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg he hη.le)
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos hdp (mul_pos hη hl))
        (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg d))
    _ = _ := by field_simp [show highEta ≠ 0 by norm_num [highEta]]

theorem boxed_sigma_pair_uniform {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3,
      ∀ a2 a3 b : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (windows j N),
        1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) →
      let W := windows j N
      (|boxedSigma20 N δ W a2 a3 b - boxedIntegral20 N δ W a2 a3 b| ≤
        epsilon * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) ∧
      (|boxedSigma21 N δ W a3 b - boxedIntegral21 N δ W a3 b| ≤
        epsilon * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) := by
  have hη := (show 0 < 10*highEta by norm_num [highEta])
  obtain ⟨T, hT4, hT⟩ := boxed_pair_unnormalized hδ hδhi (mul_pos he hη)
  refine ⟨T, hT4, ?_⟩
  intro N hN j a2 a3 b hw
  have hN2 : 2 ≤ N := by omega
  have hpoint : ∀ d ∈ boxConvolutionSupport (windows j N),
      (|boxed20 N d δ (a2 d) (a3 d) (b d) -
        (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
          J20 (a2 d) (a3 d) (b d) (omega3XPhi N d δ)| ≤
        epsilon * ((N : ℝ) / log N) / d) ∧
      (|boxed21 N d δ (a3 d) (b d) -
        (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
          J21 (a3 d) (b d) (omega3XPhi N d δ)| ≤
        epsilon * ((N : ℝ) / log N) / d) := by
    intro d hd
    obtain ⟨ha2, ha3, hb'⟩ := hw d hd
    obtain ⟨h20, h21⟩ := hT N hN j d hd (a2 d) (a3 d) (b d) ha2 ha3 hb'
    have hpay := log_scale_error_le j hN2 hδ hδhi hd he.le
    exact ⟨h20.le.trans hpay, h21.le.trans hpay⟩
  exact ⟨sigma_abs_error _ _ _ (fun d hd => (hpoint d hd).1),
    sigma_abs_error _ _ _ (fun d hd => (hpoint d hd).2)⟩

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.boxed_sigma_pair_uniform
