import FullAdmissibleCount

/-! Finite original-mother insertion. No improved upper bound is assumed. -/
noncomputable section
open Finset Real
open Wu2008DoubleSieve Wu2008DoubleSieve.SeventhEighth
open scoped Classical
namespace U8MotherInsertion

def small (N : ℕ) : Finset NinthLabel :=
  (physicalT8 N).filter fun x => (x.1.1 : ℝ) < (N : ℝ)^(1/10 : ℝ)
def large (N : ℕ) : Finset NinthLabel :=
  (physicalT8 N).filter fun x => (N : ℝ)^(1/10 : ℝ) ≤ (x.1.1 : ℝ)
def largePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (eighthPairs N).filter fun t => (N : ℝ)^(1/10 : ℝ) ≤ (t.1 : ℝ)

theorem physicalT8_card_split (N : ℕ) :
    (physicalT8 N).card = (small N).card + (large N).card := by
  have h := card_filter_add_card_filter_not (s := physicalT8 N)
    (p := fun x : NinthLabel => (x.1.1 : ℝ) < (N : ℝ)^(1/10 : ℝ))
  simpa only [not_lt, small, large] using h.symm

theorem split_disjoint (N : ℕ) : Disjoint (small N) (large N) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact (not_lt.mpr (mem_filter.mp hy).2) (mem_filter.mp hx).2

theorem large_eq_physical_pairs (N : ℕ) : large N = physical N (largePairs N) := by
  ext x
  obtain ⟨⟨a,b⟩,r⟩ := x
  simp only [large, physicalT8, physical, largePairs, mem_filter, mem_sigma, mem_range]
  tauto



theorem original_normalization {N : ℕ} (hN : 0 < N) :
    wuSingularSeries N * N / log N^(2 : ℕ) =
      MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * N / log N^(2 : ℕ) := by
  rw [wuSingularSeries_eq_liu N hN]

/-- The existing uniform half-level sieve is applied to the actual large subfamily.
The remaining classicalMass is a genuine count-weighted mass, not J8 itself. -/
theorem large_classical_mass_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((large N).card : ℝ) ≤
        ((8+ε)*wuSingularSeries N/log N)*classicalMass N (largePairs N) +
          ε*wuSingularSeries N*N/log N^(2 : ℕ) := by
  obtain ⟨T,hT,h⟩ := classicalPhysical_upper_coefficient_eight hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  rw [large_eq_physical_pairs]
  apply h N hN he
  intro p hp
  exact eighth_classicalPairGeometry (hT.trans hN) p (mem_filter.mp hp).1

/-- Actual consumption of the pre-classical mother, retaining every negative count.
This is not an improved ordinary-P2 endpoint. -/
theorem mother_with_literal_split {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullAdmissibleMother.psiCoefficient δ + 16*J7 + 8*J8 +
        8*FourRoughClosedMass.I10 + 8*FourRoughClosedMass.I11 - ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) -
        2*((physicalT7 N).card : ℝ) - ((small N).card : ℝ) - ((large N).card : ℝ) -
        ((TruncatedFourPhysical.Physical10 N).card : ℝ) -
        ((TruncatedFourPhysical.Physical11 N).card : ℝ) ≤
          (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T,hT,h⟩ := FullAdmissibleMother.truncated_fixed_all_physical_lower hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hm := h N hN he
  rw [physicalT8_card_split, Nat.cast_add] at hm
  convert hm using 1
  unfold FullAdmissibleMother.psiCoefficient
  ring




end U8MotherInsertion
