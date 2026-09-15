import MixedEtaGeometry

namespace MixedEta
open Finset Real Wu2008DoubleSieve MixedSixth
open scoped Classical Topology
noncomputable section

def complement (N n : ℕ) (δ : ℝ) : Finset (ℕ × ℕ) :=
  truncatedSixthLowerPairs N δ \
    (selected N n (lowCells δ n) ∪ selected N n (highCells δ n))

/-- Original eta coefficient: fifteen on the classical complement, one on each box. -/
def etaMass (N n : ℕ) (δ : ℝ) : ℝ :=
  15*classicalMass N δ (complement N n δ) +
    (∑ k ∈ packing N n (lowCells δ n), theta N n k δ) +
    (∑ k ∈ packing N n (highCells δ n), theta N n k δ)

/-- Exact debit identity; low orientation is changed by the proven convolution identity. -/
theorem main_eta_exact (N n : ℕ) (δ η : ℝ) :
    main N n δ η = main N n δ 0 - η*etaMass N n δ := by
  unfold main HighConsumer.mixedMain
  simp_rw [theta_swap]
  unfold truncatedSixthLowerNormalizedMain etaMass classicalMass complement selected pairBox theta
    truncatedSixthLowerC
  simp only [sub_mul,sum_sub_distrib,mul_zero,sub_zero,← mul_sum]
  ring

/-- Exact decomposition over disjoint physical prime pairs, including the entire complement. -/
theorem classical_partition {N : ℕ} {δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ) (n : ℕ) :
    classicalMass N δ (truncatedSixthLowerPairs N δ) =
      classicalMass N δ (complement N n δ) +
      classicalMass N δ (selected N n (lowCells δ n)) +
      classicalMass N δ (selected N n (highCells δ n)) := by
  obtain ⟨hl,hh,hd⟩ := actual_selected_geometry hN hδ n
  unfold classicalMass complement
  rw [add_assoc,← sum_union hd,← sum_union sdiff_disjoint,
    sdiff_union_of_subset (union_subset hl hh)]

/-- No unproved total-mass premise: factor fifteen bounds the actual full eta debit. -/
theorem etaMass_upper {N : ℕ} {δ : ℝ} (hN : 4 ≤ N) (hδ : 0 ≤ δ)
    (hlarge : (3:ℝ) ≤ (N:ℝ)^truncatedSixthLowerAlpha) (n : ℕ) :
    etaMass N n δ ≤ 15*classicalMass N δ (truncatedSixthLowerPairs N δ) := by
  have hN1 : 1 < N := by omega
  obtain ⟨hl,hh,_⟩ := actual_selected_geometry hN1 hδ n
  have hl0 := classicalMass_nonneg hN hδ hl
  have hh0 := classicalMass_nonneg hN hδ hh
  have hup := actual_theta_upper hN hδ hlarge n
  rw [classical_partition hN1 hδ n]
  unfold etaMass
  linarith only [hup,hl0,hh0]

/-- The genuine signed mother value is restored from eta=0 with a global debit.
This is uniform in every symbolic coarse resolution n and retains all labels. -/
theorem actual_main_eta_lower {N : ℕ} {δ η : ℝ} (hN : 4 ≤ N) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hlarge : (3:ℝ) ≤ (N:ℝ)^truncatedSixthLowerAlpha) (n : ℕ) :
    main N n δ 0 - 15*η*classicalMass N δ (truncatedSixthLowerPairs N δ) ≤
      main N n δ η := by
  rw [main_eta_exact N n δ η]
  have h := mul_le_mul_of_nonneg_left (etaMass_upper hN hδ hlarge n) hη
  nlinarith only [h]

end
end MixedEta
