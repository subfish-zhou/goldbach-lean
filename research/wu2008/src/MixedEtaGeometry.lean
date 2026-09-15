import MixedRecoveryTheta

namespace MixedEta
open Finset Real Wu2008DoubleSieve MixedSixth
open scoped Classical Topology
noncomputable section

/-- Exact orientation change, including repeated prime labels. -/
theorem theta_swap (N : ℕ) (Q Δ X Y : ℝ) :
    boxTheta N Q (convolutionWuWindows N Δ ![(N:ℝ)^Y,(N:ℝ)^X]) =
      boxTheta N Q (convolutionWuWindows N Δ ![(N:ℝ)^X,(N:ℝ)^Y]) := by
  have hw (a b : ℝ) : convolutionWuWindows N Δ ![a,b] =
      ![primeWindow N (a/Δ) a,primeWindow N (b/Δ) b] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun z => Fin.elim0 z) k) j
  rw [hw,hw,boxTheta,boxTheta]
  simp only [mul_div_assoc]
  rw [truncatedSixthLower_two_window_sum,truncatedSixthLower_two_window_sum]
  simp only [sum_product]
  rw [sum_comm]
  apply congrArg
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  simp only [mul_comm p q]

def pairBox (N n k : ℕ) : Finset (ℕ × ℕ) :=
  truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x N n k) (y N n k)

def selected (N n : ℕ) (K : Finset ℕ) : Finset (ℕ × ℕ) :=
  (packing N n K).biUnion (pairBox N n)

def classicalMass (N : ℕ) (δ : ℝ) (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ S, truncatedSixthLowerClassicalTheta N δ p

def theta (N n k : ℕ) (δ : ℝ) : ℝ :=
  boxTheta N ((N:ℝ)^truncatedSixthLowerC δ)
    (convolutionWuWindows N (truncatedSixthMassDelta N) ![(N:ℝ)^x N n k,(N:ℝ)^y N n k])

theorem selected_sum {N n : ℕ} (hN : 1 < N) (δ : ℝ) (K : Finset ℕ) :
    classicalMass N δ (selected N n K) =
      ∑ k ∈ packing N n K, classicalMass N δ (pairBox N n k) := by
  exact sum_biUnion (physical_pairwise hN K)

theorem classicalMass_nonneg {N : ℕ} {δ : ℝ} {S : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hS : S ⊆ truncatedSixthLowerPairs N δ) :
    0 ≤ classicalMass N δ S :=
  sum_nonneg (fun _ hp => truncatedSixthClosure_classical_theta_nonneg hN hδ (hS hp))

/-- Geometry is consumed from the concrete construction, not supplied as a binder. -/
theorem actual_selected_geometry {N : ℕ} {δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ) (n : ℕ) :
    selected N n (lowCells δ n) ⊆ truncatedSixthLowerPairs N δ ∧
    selected N n (highCells δ n) ⊆ truncatedSixthLowerPairs N δ ∧
    Disjoint (selected N n (lowCells δ n)) (selected N n (highCells δ n)) := by
  obtain ⟨hl,hp,hq,_,_,hh,hP,hQ,_,_⟩ := actual_geometry hN hδ n
  have hQb (k : ℕ) (hk : k ∈ packing N n (highCells δ n)) :
      (N:ℝ)^truncatedSixthLowerBeta ≤ (N:ℝ)^y N n k/truncatedSixthMassDelta N :=
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le)
      (show truncatedSixthLowerBeta ≤ (1:ℝ)/4 by norm_num [truncatedSixthLowerBeta])).trans (hQ k hk)
  refine ⟨?_,?_,?_⟩
  · intro p hp'
    obtain ⟨k,hk,hpk⟩ := mem_biUnion.mp hp'
    exact HighConsumer.retained_box_subset hN (hl k hk).1 (hp k hk) (hq k hk) hpk
  · intro p hp'
    obtain ⟨k,hk,hpk⟩ := mem_biUnion.mp hp'
    exact HighConsumer.retained_box_subset hN (hh k hk).1 (hP k hk) (hQb k hk) hpk
  · apply disjoint_left.mpr
    intro p hp' hq'
    obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp hp'
    obtain ⟨j,hj,hpj⟩ := mem_biUnion.mp hq'
    exact disjoint_left.mp (HighConsumer.low_high_disjoint hN hδ (hl i hi) (hQ j hj)) hpi hpj

/-- All actual low and high labels receive the genuine factor-four upper bound. -/
theorem actual_theta_upper {N : ℕ} {δ : ℝ} (hN : 4 ≤ N) (hδ : 0 ≤ δ)
    (hlarge : (3:ℝ) ≤ (N:ℝ)^truncatedSixthLowerAlpha) (n : ℕ) :
    (∑ k ∈ packing N n (lowCells δ n), theta N n k δ) +
      (∑ k ∈ packing N n (highCells δ n), theta N n k δ) ≤
    4*(classicalMass N δ (selected N n (lowCells δ n)) +
      classicalMass N δ (selected N n (highCells δ n))) := by
  have hN1 : 1 < N := by omega
  obtain ⟨hl,hp,hq,_,_,hh,hP,hQ,_,_⟩ := actual_geometry hN1 hδ n
  rw [selected_sum hN1,selected_sum hN1,mul_add,mul_sum,mul_sum]
  apply add_le_add
  · apply sum_le_sum
    intro k hk
    exact MixedRecovery.box_theta_upper hN hδ (hl k hk).1 (hp k hk) (hq k hk) hlarge
  · apply sum_le_sum
    intro k hk
    apply MixedRecovery.box_theta_upper hN hδ (hh k hk).1 (hP k hk) _ hlarge
    exact (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le)
      (show truncatedSixthLowerBeta ≤ (1:ℝ)/4 by norm_num [truncatedSixthLowerBeta])).trans (hQ k hk)

end
end MixedEta
