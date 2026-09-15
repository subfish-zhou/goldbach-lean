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

/-- The cutoff belongs to the large piece; the original r=b diagonal stays. -/
theorem mem_large {N a b r : ℕ} :
    (⟨(a,b),r⟩ : NinthLabel) ∈ large N ↔
      (a,b) ∈ lowerPairs N N (z N) (v N) ∧ (a : ℝ) < v N ∧
      r < N+1 ∧ r.Prime ∧ b ≤ r ∧ a*b*r < N ∧
      (N-a*b*r).Prime ∧ (N : ℝ)^(1/10 : ℝ) ≤ (a : ℝ) := by
  rw [large, mem_filter, mem_physicalT8]
  tauto

/-- A finite-source witness shared with the modern lane; no analytic import is moved. -/
theorem small_closed_formula (N : ℕ) : small N =
    ((((((Finset.range ⌈(N : ℝ)+1⌉₊).filter
      (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N : ℝ)^(100/1327 : ℝ) ≤ (q : ℝ))) ×ˢ
      ((Finset.range ⌈(N : ℝ)+1⌉₊).filter
      (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N : ℝ)^(1/3 : ℝ) ≤ (q : ℝ)))).filter
      (fun t => t.1 < t.2 ∧ t.1*t.2^2 < N)).filter
      (fun t => (t.1 : ℝ) < (N : ℝ)^(1/3 : ℝ))).sigma
      (fun t => (Finset.range (N+1)).filter
      (fun r => r.Prime ∧ t.2 ≤ r ∧ t.1*t.2*r < N ∧ (N-t.1*t.2*r).Prime))).filter
      (fun x => (x.1.1 : ℝ) < (N : ℝ)^(1/10 : ℝ)) := rfl

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

/-- Algebra only: replacing the small coefficient keeps the large coefficient once.
There is intentionally no count-upper premise and no claimed gain endpoint. -/
theorem signed_coefficient_replacement (B L H W : ℝ) :
    B - 8*(L+H) + (8*L-(36/5)*W) = B - ((36/5)*W+8*H) := by ring

theorem ordinary_coefficient_replacement (B L H W : ℝ) :
    (B - ((36/5)*W+8*H))/4 = (B-8*(L+H))/4 + (8*L-(36/5)*W)/4 := by ring

theorem old_to_new_small_weight (x : ℝ) :
    (36/5 : ℝ)/(1-x) = 8*((9/10 : ℝ)/(1-x)) := by ring

end U8MotherInsertion
