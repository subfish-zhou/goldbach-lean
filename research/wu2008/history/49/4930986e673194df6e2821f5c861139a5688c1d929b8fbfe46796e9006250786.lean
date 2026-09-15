import RMapMFifthGain

namespace WuPaper.RMapMFifth
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open WuTarget.Wu08FifthSource WuSource.SrcFifthGain
open scoped Interval
noncomputable section

theorem original_fifth_directed_lower {δ c eC rhoC : ℝ} {pC : ℝ → ℝ}
    {h q e : ℕ → ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) (heC : 0 ≤ eC)
    (hpC : ContinuousOn pC (Icc s0 FifthClassicalShape.q))
    (hC : ∀ s ∈ Icc s0 FifthClassicalShape.q, |wuLowerCoefficient s-pC s| ≤ eC)
    (hquadC : |8*(∫ s in s0..FifthClassicalShape.q, pC s*weight s)-c| ≤ rhoC)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hh : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    (hquadG : ∀ j < 13, |cellWeight j-q j| ≤ e j) :
    (c-rhoC-10*eC)+(8*∑ j ∈ Finset.range 13, (q j-e j)*h (15+j)) ≤
      paperClassical+sourceGain (wuImprovementLimit false δ) :=
  add_le_add (classical_directed_lower heC hpC hC hquadC)
    (gain_weight_error_lower hδ hd hn hh hquadG)

set_option pp.fullNames true
#check @original_fifth_directed_lower
#print axioms original_fifth_directed_lower
#check @source_parameter_branches
#print axioms source_parameter_branches
#check @interval_error
#print axioms interval_error
#check @recurrence_inner_error
#print axioms recurrence_inner_error
#check @recurrence_outer_error
#print axioms recurrence_outer_error
#check @coefficient_nested_error
#print axioms coefficient_nested_error
#check @classical_eight_error
#print axioms classical_eight_error
#check @classical_directed_lower
#print axioms classical_directed_lower
#check @cross_cell_error
#print axioms cross_cell_error
#check @cell_weight_enclosure
#print axioms cell_weight_enclosure
#check @cell_weight_directed_enclosure
#print axioms cell_weight_directed_enclosure
#check @grid_error
#print axioms grid_error
#check @gain_directed_enclosures
#print axioms gain_directed_enclosures
#check @gain_weight_error_lower
#print axioms gain_weight_error_lower
#check @Wu2008DoubleSieve.wuImprovementLimit_lower_antitone
#print axioms Wu2008DoubleSieve.wuImprovementLimit_lower_antitone
#check @Wu2008DoubleSieve.wuImprovementLimit_nonneg
#print axioms Wu2008DoubleSieve.wuImprovementLimit_nonneg

end
end WuPaper.RMapMFifth
