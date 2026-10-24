import WR2GammaHighLowerTripleGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitActualFamily

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighBoxRecovery Finset
open scoped Classical

/-- Literal five- and six-prime words, with every prefix label retained. -/
def sourceFamily (j : Fin 3) (N : ℕ) (δ : ℝ) (high : Bool) :
    LabelledPhysical.Family Profile N :=
  actualFamily N δ (Wu04RemainingCore.row j) (windows j N) high
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hd)

theorem original_partition (j : Fin 3) (N : ℕ) (δ : ℝ) (high : Bool) :
    gamma j N δ (if high then 21 else 20) =
      actualUnit N δ (Wu04RemainingCore.row j) (windows j N) high +
      actualSource N δ (Wu04RemainingCore.row j) (windows j N) high :=
  (actual_partition N δ (Wu04RemainingCore.row j) (windows j N) high).symm

/-- Only the original nonunit part is enlarged by the physical prime mass. -/
theorem actual_source_upper {N : ℕ} (j : Fin 3) (δ : ℝ) (high : Bool)
    (hN : 4 ≤ N) (he : Even N) :
    gamma j N δ (if high then 21 else 20) ≤
      actualUnit N δ (Wu04RemainingCore.row j) (windows j N) high +
      (sourceFamily j N δ high).primeMass := by
  rw [original_partition]
  apply add_le_add le_rfl
  unfold sourceFamily
  rw [(actualFamily_dictionary N δ (Wu04RemainingCore.row j) (windows j N) high _).1]
  exact source_le_envelope
    (fun _ hm => boxConvolutionSupport_pos (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hm)
    hN he (word_length high) (word_last high)

/-- Every physical profile has a uniform power gap, including empty output fibres. -/
theorem source_geometry {N : ℕ} {δ : ℝ} (j : Fin 3) (high : Bool)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) {x : Profile}
    (hx : x ∈ (sourceFamily j N δ high).labels) :
    PhysicalGeometry N highEta (sourceFamily j N δ high) x := by
  have hprof : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high :=
    (mem_filter.mp hx).1
  obtain ⟨hm,_,hq,_,_,hcap⟩ := profile_data hprof
  have hlarge := LowerTriple.window_lower j hN hd hh hm hq
  have hg := (sourceFamily j N δ high).geometry x hx
  have hpos : 0 < cofactor x := hg.1
  have hle : cofactor x ≤ N := (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N:ℝ)^highEta ≤ cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (penultimate_dvd x))
  exact ⟨hpos,hle,hpow,omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1,hlarge.2.trans (le_max_left _ _),hg.2.2.1,hg.2.2.2⟩

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.actual_source_upper
#print axioms WuPaper.R2GammaHigh.Tail.source_geometry
