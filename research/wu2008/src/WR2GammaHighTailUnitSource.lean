import WR2GammaHighTailUnitLimit

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnit HighUnitSource
open scoped Classical

theorem source_pair_le_boxed {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (a0 a1 a2 a3 b : ℕ → ℝ)
    (hw : ∀ d ∈ boxConvolutionSupport (windows j N),
      1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) :
    let W := windows j N
    unit20 N δ W a0 a1 a2 a3 b ≤ boxedSigma20 N δ W a2 a3 b ∧
    unit21 N δ W a0 a1 a2 a3 b ≤ boxedSigma21 N δ W a3 b := by
  have hdpos : ∀ d ∈ boxConvolutionSupport (windows j N), 0 < d :=
    fun _ hd => boxConvolutionSupport_pos
      (fun j p hp => (mem_primeWindow.mp hp).1.pos) hd
  have hR : ∀ d ∈ boxConvolutionSupport (windows j N),
      1 < (N : ℝ) ^ (1 / 2 - δ) / d :=
    fun _ hd => (LowerTriple.phi_bounds j hN hδ hδhi hd).2.1
  constructor
  · simpa only [unit20, boxedSigma20, boxed20] using
      (source_le20 (N := N) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b := b)
        hdpos hR (fun d hd => (hw d hd).1) (fun d hd => (hw d hd).2.2))
  · simpa only [unit21, boxedSigma21, boxed21] using
      (source_le21 (N := N) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b := b)
        hdpos hR (fun d hd => (hw d hd).2.1) (fun d hd => (hw d hd).2.2))

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.source_pair_le_boxed
