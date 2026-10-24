import WR2GammaHighLowerTripleGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitActualFamily

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Real Finset
open scoped Classical

/-- The four original words use the same supported high-window convolution. -/
def sourceFamily (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 4) :
    LabelledPhysical.Family Gamma16Profile N :=
  actualFamily N δ (Wu04RemainingCore.row j) (windows j N) k
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hd)

/-- Exact unit/nonunit partition, before any analytic estimate. -/
theorem original_partition (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 4) :
    gamma j N δ (16+k.val) =
      FourPrimeUnit.actualSource N δ (Wu04RemainingCore.row j) (windows j N) k +
      secondFunctionalFourPrimeNonunitSum (Wu04RemainingCore.row j) N δ (windows j N) k := by
  exact (FourPrimeUnit.actual_gamma_partition N δ (Wu04RemainingCore.row j) (windows j N) k).symm

/-- No original unit contribution is discarded in the physical source bound. -/
theorem actual_source_upper {N : ℕ} (j : Fin 3) (δ : ℝ) (k : Fin 4)
    (hN : 4 ≤ N) (he : Even N) :
    gamma j N δ (16+k.val) ≤
      FourPrimeUnit.actualSource N δ (Wu04RemainingCore.row j) (windows j N) k +
      (sourceFamily j N δ k).primeMass := by
  rw [original_partition]
  apply add_le_add le_rfl
  unfold sourceFamily
  rw [(actualFamily_dictionary N δ (Wu04RemainingCore.row j) (windows j N) k _).1]
  exact FourPrimeNonunit.actual_source_le _ _
    (fun _ hm => boxConvolutionSupport_pos (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hm) hN he k

/-- Power-gap geometry holds on every retained nonunit label. -/
theorem source_geometry {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) {x : Gamma16Profile}
    (hx : x ∈ (sourceFamily j N δ k).labels) :
    PhysicalGeometry N highEta (sourceFamily j N δ k) x := by
  have hprof : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k :=
    (mem_filter.mp hx).1
  obtain ⟨hm,h3,_,_,_,_,_,_,_,_,hcap⟩ := profile_data hprof
  have hlarge := LowerTriple.window_lower j hN hd hh hm h3
  have hg := (sourceFamily j N δ k).geometry x hx
  have hpos : 0 < gamma16Cofactor x := hg.1
  have hle : gamma16Cofactor x ≤ N :=
    (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N:ℝ)^highEta ≤ gamma16Cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (penultimate_dvd x))
  exact ⟨hpos,hle,hpow,omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1,hlarge.2.trans (le_max_left _ _),hg.2.2.1,hg.2.2.2⟩

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.actual_source_upper
#print axioms WuPaper.R2GammaHigh.Four.source_geometry
