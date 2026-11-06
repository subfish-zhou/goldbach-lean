import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassIntegral

/-!
# The actual count lower bound from a constructed coarse rectangle

The packing in the accepted finite theorem is instantiated, not supplied
as a hypothesis. Negative perturbed effective coefficients are replaced
by zero by choosing the empty packing.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem truncatedSixthMass_wedge_rectangle_packing {δ η ε a b c d s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (hab : a ≤ b) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hc : truncatedSixthLowerBeta ≤ c)
    (hbd : truncatedSixthLowerAdmissibleRegion δ b d)
    (hs2 : 2 ≤ s) (hs5 : s ≤ 5) (hs : s ≤ truncatedSixthLowerS δ b d) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerWedgePairs N δ) +
        (wuLowerCoefficient s + wuImprovementLimit false δ s - η) *
          truncatedSixthMassPackingTheta N δ a b c d -
        ε * truncatedSixthMassScale N ≤
        (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
          ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
          ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T, hT, h⟩ := truncatedSixthLower_finite_packing_actual hδ hδhi hη hηhi hε {s}
    (by intro t ht; have he := Finset.mem_singleton.mp ht; subst t; exact ⟨hs2, hs5⟩)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hN1 : 1 < N := by omega
  let J := truncatedSixthMassPacking N a b c d
  let I := J.image (fun j => Nat.pair j.1 j.2)
  let x := fun n => truncatedSixthMassGridPoint N a ((Nat.unpair n).1 + 1)
  let y := fun n => truncatedSixthMassGridPoint N c ((Nat.unpair n).2 + 1)
  have hJ (n : ℕ) (hn : n ∈ I) : Nat.unpair n ∈ J := by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    simpa using hj
  have hgeom (n : ℕ) (hn : n ∈ I) :=
    truncatedSixthMass_packing_admissible hN1 hab hcd ha hc hbd (hJ n hn)
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ)
      (fun n => truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x n) (y n)) := by
    intro n _ m _ hnm
    apply truncatedSixthMass_packing_disjoint hN1 a c
    intro heq
    apply hnm
    simpa using congrArg (fun j : ℕ × ℕ => Nat.pair j.1 j.2) heq
  have hcount := h N hN he (truncatedSixthMassDelta N)
    (truncatedSixthMass_delta_legal hN1).2.1 (truncatedSixthMass_delta_legal hN1).2.2
    I x y (fun _ => s)
    (fun n hn => (hgeom n hn).1)
    (fun n hn => (hgeom n hn).2.1)
    (fun n hn => (hgeom n hn).2.2)
    (fun n hn => ⟨Finset.mem_singleton_self s,
      truncatedSixthMass_packing_grid_parameter hN1 hab hcd hs (hJ n hn)⟩)
    hdisj
  have hsum :
      (∑ n ∈ I, (wuLowerCoefficient s + wuImprovementLimit false δ s - η) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N (truncatedSixthMassDelta N)
            ![(N : ℝ) ^ y n, (N : ℝ) ^ x n])) =
      (wuLowerCoefficient s + wuImprovementLimit false δ s - η) *
        truncatedSixthMassPackingTheta N δ a b c d := by
    dsimp [I]
    rw [sum_image]
    · simp only [Nat.unpair_pair, x, y]
      rw [truncatedSixthMassPackingTheta, mul_sum]
      rfl
    · intro u _ v _ huv
      simpa using congrArg Nat.unpair huv
  rw [hsum] at hcount
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hcount

theorem truncatedSixthMass_wedge_actual {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerWedgePairs N δ) -
        ε * truncatedSixthMassScale N ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T, hT, h⟩ := truncatedSixthLower_normalized_masked_relative hδ hη hηhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hw : truncatedSixthLowerWedgePairs N δ ⊆ truncatedSixthLowerPairs N δ :=
    filter_subset _ _
  have hcount := (h N hN he _ hw).trans
    (truncatedSixthLower_mask_mass_le (by omega) hδ _ hw)
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hcount


end Wu2008DoubleSieve
