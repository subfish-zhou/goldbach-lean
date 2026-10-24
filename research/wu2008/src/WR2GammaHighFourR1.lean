import WR2GammaHighFourFibre
import Wu08FourMotherRelative
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Real Finset
open scoped Classical

theorem restricted_R1_log_bound {δ A : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ k : Fin 4, ∀ P : Gamma16Profile → Prop, ∀ Z : ℝ,
        ((sourceFamily j N δ k).restrictLabels P).R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ C*N/log (N : ℝ)^A := by
  obtain ⟨C,hC,T,hT,hc⟩ := LabelledPhysical.Family.R1_log_saving A highEta
    ((max 1 (1/highEta))^4) hA (by norm_num [highEta]) (by positivity) hd
  refine ⟨C,hC,T,hT,fun N hN j k P Z => ?_⟩
  have hN2 : 2 ≤ N := by omega
  apply hc N hN Gamma16Profile ((sourceFamily j N δ k).restrictLabels P) ?_ ?_ ?_ Z
  · intro x hx
    have hg := source_geometry j k hN2 hd hh (mem_filter.mp hx).1
    exact ⟨hg.power_lower,hg.power_upper⟩
  · intro x hx
    have hprof : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k :=
      (mem_filter.mp (mem_filter.mp hx).1).1
    have hm := (profile_data hprof).1
    change (1 : ℝ) ≤ (convolutionCoeff (windows j N) x.1 : ℝ)
    exact_mod_cast mem_boxConvolutionSupport.mp hm
  · intro E
    exact ((sourceFamily j N δ k).restrictLabels_fibre_le P E).trans
      (fixed_cofactor_bound j k hN2 hd hh E)

theorem restricted_R1_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 4, ∀ P : Gamma16Profile → Prop, ∀ Z : ℝ,
      ((sourceFamily j N δ k).restrictLabels P).R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,T0,hT0,hc⟩ := restricted_R1_log_bound hd hh (by norm_num : (0 : ℝ)<3)
  obtain ⟨T1,_,hp⟩ := Wu08FourMother.raw_error_paid (div_pos he hC)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),fun N hN j k P Z => ?_⟩
  have hb := hc N (by omega) j k P Z
  norm_num at hb
  calc
    _ ≤ C*N/log (N : ℝ)^3 := hb
    _ = C*((N : ℝ)/log (N : ℝ)^3) := by ring
    _ ≤ C*((ε/C)*U8CanonicalMother.M N) := mul_le_mul_of_nonneg_left (hp N (by omega)) hC.le
    _ = ε*truncatedSixthMassScale N := by
      rw [← mul_assoc, mul_div_cancel₀ ε hC.ne']
      rfl


end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.restricted_R1_paid
