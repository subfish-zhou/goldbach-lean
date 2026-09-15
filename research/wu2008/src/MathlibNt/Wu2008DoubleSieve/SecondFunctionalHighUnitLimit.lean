import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitMaskedPhysical
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighIdentification

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnit
open SecondFunctionalUnitPrimeFibre

/-- The literal closed physical envelope converges to the independent D20 unit section.
The threshold is uniform over every window satisfying the two external bounds. -/
theorem physical20_uniform (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (a2 a3 b phi : ℝ),
      1/10 ≤ a2 → b ≤ 1/2 →
      |Real.log R / R^phi *
        (∑ f ∈ primePrefix20 R a2 a3 b,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last 3)).val (R^b)).card : ℝ)) -
        J20 a2 a3 b phi| < epsilon := by
  obtain ⟨T,hT,h⟩ := SecondFunctionalUnitMasked.physical_uniform 3 6 C20 normalized20 epsilon he
  refine ⟨T,hT,?_⟩
  intro R hR a2 a3 b phi ha hb
  have h' := h R hR phi b (gamma20 a2 a3 b) flags20
  simpa only [SecondFunctionalUnitMasked.selected,
    ← primePrefix20_exact (hT.trans_le hR) a2 a3 b,
    ← J20_identification ha hb phi] using h'

/-- The same endpoint for D21, with its full labelled five-prime prefix. -/
theorem physical21_uniform (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (a3 b phi : ℝ),
      1/10 ≤ a3 → b ≤ 1/2 →
      |Real.log R / R^phi *
        (∑ f ∈ primePrefix21 R a3 b,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last 4)).val (R^b)).card : ℝ)) -
        J21 a3 b phi| < epsilon := by
  obtain ⟨T,hT,h⟩ := SecondFunctionalUnitMasked.physical_uniform 4 6 C21 normalized21 epsilon he
  refine ⟨T,hT,?_⟩
  intro R hR a3 b phi ha hb
  have h' := h R hR phi b (gamma21 a3 b) flags21
  simpa only [SecondFunctionalUnitMasked.selected,
    ← primePrefix21_exact (hT.trans_le hR) a3 b,
    ← J21_identification ha hb phi] using h'

/-- One threshold for both envelopes, retaining the same phi in both sections.
Each error is below epsilon; this does not claim their sum is below epsilon. -/
theorem physical_pair_uniform (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (a2 a3 b phi : ℝ),
      1/10 ≤ a2 → 1/10 ≤ a3 → b ≤ 1/2 →
      (|Real.log R / R^phi *
        (∑ f ∈ primePrefix20 R a2 a3 b,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last 3)).val (R^b)).card : ℝ)) -
        J20 a2 a3 b phi| < epsilon) ∧
      (|Real.log R / R^phi *
        (∑ f ∈ primePrefix21 R a3 b,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last 4)).val (R^b)).card : ℝ)) -
        J21 a3 b phi| < epsilon) := by
  obtain ⟨T20,h20,p20⟩ := physical20_uniform epsilon he
  obtain ⟨T21,_,p21⟩ := physical21_uniform epsilon he
  refine ⟨max T20 T21, h20.trans_le (le_max_left _ _), ?_⟩
  intro R hR a2 a3 b phi ha2 ha3 hb
  exact ⟨p20 R ((le_max_left _ _).trans hR) a2 a3 b phi ha2 hb,
    p21 R ((le_max_right _ _).trans hR) a3 b phi ha3 hb⟩

end Wu2008DoubleSieve.HighUnit
