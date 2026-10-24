import WR2GammaHighTailUnitFibre
import Wu08FourMotherRelative
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve HighBoxRecovery Real Finset
open scoped Classical

theorem source_R1_log_saving {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∃ hT : 4 ≤ T,
      ∀ (N : ℕ) (hN : T ≤ N),
      ∀ row : Fin 3,
      ∀ (n : ℕ), n ≤ 5 →
      ∀ (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ)^(1/2-δ)/d)))
        (j : Fin n) (b : ℕ → ℝ) (Z : ℝ),
      (sourceFamily row (by omega : 2 ≤ N) hδ hδhi P j b).R1
        (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ C*N / log (N : ℝ)^A := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨C,hC,T,hT,hd⟩ := LabelledPhysical.Family.R1_log_saving A highEta
    ((max 1 (1/highEta))^6) hA hη (by positivity) hδ
  refine ⟨C,hC,T,hT,?_⟩
  intro N hN row n hn P j b Z
  have hN2 : 2 ≤ N := by omega
  have hg := family_facts row hN2 hδ hδhi P j b
  apply hd N hN _ (sourceFamily row hN2 hδ hδhi P j b) _ _ _ Z
  · intro c hc
    exact ⟨(hg.1 c hc).1.power_lower,(hg.1 c hc).1.power_upper⟩
  · intro c hc
    change (1 : ℝ) ≤ (convolutionCoeff (windows row N) c.1 : ℝ)
    exact_mod_cast coefficient_pos hc
  · intro e
    exact (hg.2 e).trans (pow_le_pow_right₀ (le_max_left _ _) (by omega))

theorem source_R1_paid {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, ∃ hT : 4 ≤ T,
      ∀ (N : ℕ) (hN : T ≤ N),
      ∀ row : Fin 3,
      ∀ (n : ℕ), n ≤ 5 →
      ∀ (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ)^(1/2-δ)/d)))
        (j : Fin n) (b : ℕ → ℝ) (Z : ℝ),
      (sourceFamily row (by omega : 2 ≤ N) hδ hδhi P j b).R1
        (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,T0,hT0,hc⟩ := source_R1_log_saving hδ hδhi (by norm_num : (0:ℝ)<3)
  obtain ⟨T1,_,hp⟩ := Wu08FourMother.raw_error_paid (div_pos he hC)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN row n hn P j b Z
  have hb := hc N (by omega) row n hn P j b Z
  norm_num at hb
  calc
    _ ≤ C*N/log (N:ℝ)^3 := hb
    _ = C*((N:ℝ)/log (N:ℝ)^3) := by ring
    _ ≤ C*((ε/C)*U8CanonicalMother.M N) := mul_le_mul_of_nonneg_left (hp N (by omega)) hC.le
    _ = ε*truncatedSixthMassScale N := by
      rw [← mul_assoc,mul_div_cancel₀ ε hC.ne']
      rfl

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.source_R1_log_saving
#print axioms WuPaper.R2GammaHigh.TailUnit.source_R1_paid
