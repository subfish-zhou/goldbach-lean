import WR2GammaHighTailSource
import WR2GammaHighLowerTripleClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceIntegral

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnit HighUnitSource HighBoxRecovery Real Filter
open scoped Classical Topology

theorem boxed_pair_uniform {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3,
      ∀ d ∈ boxConvolutionSupport (windows j N),
      ∀ a2 a3 b : ℝ, 1/10 ≤ a2 → 1/10 ≤ a3 → b ≤ 1/2 →
        let R := (N : ℝ) ^ (1 / 2 - δ) / d
        (|log R / ((N : ℝ) / d) * boxed20 N d δ a2 a3 b -
          J20 a2 a3 b (omega3XPhi N d δ)| < epsilon) ∧
        (|log R / ((N : ℝ) / d) * boxed21 N d δ a3 b -
          J21 a3 b (omega3XPhi N d δ)| < epsilon) := by
  obtain ⟨R0, _, hp⟩ := physical_pair_uniform epsilon he
  have hη := (show 0 < 10*highEta by norm_num [highEta])
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN j d hd a2 a3 b ha2 ha3 hb'
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := LowerTriple.phi_bounds j (by omega) hδ hδhi hd
  have hd0 := boxConvolutionSupport_pos
    (fun j p hp => (mem_primeWindow.mp hp).1.pos) hd
  have hs := boxed_scale_identity (by omega : 0 < N) hd0 hg.2.1
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hg.1
  have h := hp _ hlarge a2 a3 b (omega3XPhi N d δ) ha2 ha3 hb'
  simpa only [hs, boxed20, boxed21] using h

theorem boxed_pair_unnormalized {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3,
      ∀ d ∈ boxConvolutionSupport (windows j N),
      ∀ a2 a3 b : ℝ, 1/10 ≤ a2 → 1/10 ≤ a3 → b ≤ 1/2 →
        let R := (N : ℝ) ^ (1 / 2 - δ) / d
        (|boxed20 N d δ a2 a3 b - (N : ℝ) / ((d : ℝ) * log R) *
          J20 a2 a3 b (omega3XPhi N d δ)| <
            (N : ℝ) / ((d : ℝ) * log R) * epsilon) ∧
        (|boxed21 N d δ a3 b - (N : ℝ) / ((d : ℝ) * log R) *
          J21 a3 b (omega3XPhi N d δ)| <
            (N : ℝ) / ((d : ℝ) * log R) * epsilon) := by
  obtain ⟨T, hT4, hT⟩ := boxed_pair_uniform hδ hδhi he
  refine ⟨T, hT4, ?_⟩
  intro N hN j d hd a2 a3 b ha2 ha3 hb'
  have hN4 : 4 ≤ N := hT4.trans hN
  have hg := LowerTriple.phi_bounds j (by omega) hδ hδhi hd
  have hd0 := boxConvolutionSupport_pos
    (fun j p hp => (mem_primeWindow.mp hp).1.pos) hd
  obtain ⟨h20, h21⟩ := hT N hN j d hd a2 a3 b ha2 ha3 hb'
  exact ⟨unnormalize (by omega) hd0 hg.2.1 h20,
    unnormalize (by omega) hd0 hg.2.1 h21⟩

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.boxed_pair_unnormalized
