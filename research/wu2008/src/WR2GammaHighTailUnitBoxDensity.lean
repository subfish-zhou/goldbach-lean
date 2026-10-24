import WR2GammaHighTailUnitEnvelope

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve HighUnit HighUnitPrimeOutput Real Finset
open scoped Classical

theorem envelope_pair_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ row : Fin 3,
      ∀ a2 a3 b : ℕ → ℝ,
      envelope20 N (windows row N) (fun d => (N:ℝ)^(1/2-δ)/d) a2 a3 b +
        envelope21 N (windows row N) (fun d => (N:ℝ)^(1/2-δ)/d) a3 b ≤
      (boxedSigma20 N δ (windows row N) a2 a3 b + boxedSigma21 N δ (windows row N) a3 b)*
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
        ε*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := family_density hd hh hr (half_pos he)
  refine ⟨T,hT,?_⟩
  intro N hN hn row a2 a3 b
  have hN2 : 2 ≤ N := by omega
  let R := fun d : ℕ => (N:ℝ)^(1/2-δ)/d
  have hp : ∀ d ∈ boxConvolutionSupport (windows row N), 0 < d :=
    fun _ hm => boxConvolutionSupport_pos (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hm
  have hR : ∀ d ∈ boxConvolutionSupport (windows row N), 1 < R d :=
    fun _ hm => (LowerTriple.phi_bounds row hN2 hd hh hm).2.1
  have h20 := h N hN hn row 4 (by omega)
    (fun d => primePrefix20 (R d) (a2 d) (a3 d) (b d)) (Fin.last 3) b
  have h21 := h N hN hn row 5 (by omega)
    (fun d => primePrefix21 (R d) (a3 d) (b d)) (Fin.last 4) b
  dsimp only at h20 h21
  rw [sourceFamily_primeMass,sourceFamily_mass] at h20 h21
  have he20 := envelope20_interval (N := N) (windows row N) R a2 a3 b hp hR
  have he21 := envelope21_interval (N := N) (windows row N) R a3 b hp hR
  have hm20 := boxedSigma20_interval (δ := δ) (windows row N) a2 a3 b hp hR
  have hm21 := boxedSigma21_interval (δ := δ) (windows row N) a3 b hp hR
  change envelope20 _ _ _ _ _ _ = outputMass _ _ _ _ _ at he20
  change envelope21 _ _ _ _ _ = outputMass _ _ _ _ _ at he21
  change boxedSigma20 _ _ _ _ _ _ = intervalMass _ _ _ _ _ at hm20
  change boxedSigma21 _ _ _ _ _ = intervalMass _ _ _ _ _ at hm21
  rw [he20,he21,hm20,hm21]
  dsimp only [family20,family21,R] at h20 h21 ⊢
  linarith only [h20,h21]

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.envelope_pair_density
