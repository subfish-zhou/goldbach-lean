import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIRectangularAspectGate
import MathlibNt.AnalyticNumberTheory.LargeSieve.ProductionDyadicConductorGeometry

/-!
# Conductor-cell local actual Vaughan Type-II shells

This checker leaf performs only the finite conductor-cell compilation needed to
apply the rectangular aspect gate at `Q = 2 * i`.  In particular, the
coefficient-`L¹` family term remains the literal term over the actual cell, and
the complementary filtered family is called residual rather than extreme.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The AP-normalized actual collected-shell mean restricted to an arbitrary
finite conductor set. -/
def apNormalizedVaughanActualCollectedShellMeanOn
    (N u v k l : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)

/-- Exact block normalization: on a conductor cell with lower endpoint `i`,
`1 / φ(q) = (1 / q) (q / φ(q))` pays at most `1 / i`. -/
theorem apNormalizedVaughanActualCollectedShellMeanOn_le_inv_mul_weightedMean
    (N u v k l i : ℕ) (S : Finset ℕ) (hi : 0 < i)
    (hlevels : ∀ q ∈ S, i ≤ q) :
    apNormalizedVaughanActualCollectedShellMeanOn N u v k l S ≤
      (1 / (i : ℝ)) *
        vaughanActualCanonicalCollectedShellWeightedMean N u v k l S := by
  unfold apNormalizedVaughanActualCollectedShellMeanOn
    vaughanActualCanonicalCollectedShellWeightedMean
    vaughanActualCanonicalCollectedShellAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hq0 : 0 < q := hi.trans_le (hlevels q hq)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq0
  have hsum : 0 ≤ ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ) := by
    positivity
  have hinv : (1 / (q : ℝ)) ≤ 1 / (i : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hi)
      (by exact_mod_cast hlevels q hq)
  calc
    ((q.totient : ℝ)⁻¹) *
        (∑ χ : PrimitiveCharacter q,
          Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)) =
      (1 / (q : ℝ)) *
        (((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : PrimitiveCharacter q,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ))) := by
        field_simp
    _ ≤ (1 / (i : ℝ)) *
        (((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : PrimitiveCharacter q,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ))) := by
      exact mul_le_mul_of_nonneg_right hinv
        (mul_nonneg (div_nonneg (by positivity) (by positivity)) hsum)

/-- A conductor cell contained in `Ioc i (2*i)` is controlled by the existing
aspect gate with its parameter set literally to `2*i`.  The sharp rectangular
coefficient-`L¹` family term is retained over `G.cell i`. -/
theorem apNormalizedVaughanActualCollectedShellMeanOn_cell_le_aspectGate
    (N Q C u v k l i : ℕ) (H : ℝ)
    (G : ProductionConductorBlockGeometry N Q C)
    (hi : i ∈ G.index)
    (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 3 ≤ N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v)
    (hH : 0 ≤ H)
    (hAspect :
      (vaughanTypeIIRectangularD k : ℝ) +
          (vaughanTypeIIRectangularX N k : ℝ) ≤
        H * (((N : ℝ) / ((2 * i : ℕ) : ℝ) ^ 2) +
          (((2 * i : ℕ) : ℝ) ^ 2))) :
    apNormalizedVaughanActualCollectedShellMeanOn N u v k l (G.cell i) ≤
      (1 / (i : ℝ)) *
        ((1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
          (primitiveBilinearQFactor (2 * i) *
            Real.sqrt (27 * (H + 1) *
              Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) *
            ((N : ℝ) + (((2 * i : ℕ) : ℝ) ^ 2) * Real.sqrt N)) +
        (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
          vaughanTypeIIRectangularL1exp N k l *
            weightedPrimitiveFamilyMass (G.cell i)) := by
  have hi0 : 0 < i := G.lower_pos i hi
  have h2i : 0 < 2 * i := Nat.mul_pos (by omega) hi0
  have hlevels : ∀ q ∈ G.cell i, i ≤ q := by
    intro q hq
    exact (Finset.mem_Ioc.mp (hcell hq)).1.le
  have hS : G.cell i ⊆ Finset.Icc 1 (2 * i) := by
    intro q hq
    have hqIoc := Finset.mem_Ioc.mp (hcell hq)
    exact Finset.mem_Icc.mpr ⟨by omega, hqIoc.2⟩
  refine (apNormalizedVaughanActualCollectedShellMeanOn_le_inv_mul_weightedMean
    N u v k l i (G.cell i) hi0 hlevels).trans ?_
  exact mul_le_mul_of_nonneg_left
    (vaughanActualCanonicalCollectedShellWeightedMean_le_aspectGate
      N (2 * i) u v k l H hN h2i (G.cell i) hS hactive hH hAspect)
    (by positivity)

/-- The concrete production dyadic cell satisfies the `Ioc i (2*i)` interface,
so no geometric premise remains at this call site. -/
theorem apNormalizedVaughanActualCollectedShellMeanOn_productionCell_le_aspectGate
    (N Q C u v k l i : ℕ) (H : ℝ)
    (hR : 0 < logConductorThreshold N C)
    (hi : i ∈ (productionConductorBlockGeometry N Q C hR).index)
    (hN : 3 ≤ N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v)
    (hH : 0 ≤ H)
    (hAspect :
      (vaughanTypeIIRectangularD k : ℝ) +
          (vaughanTypeIIRectangularX N k : ℝ) ≤
        H * (((N : ℝ) / ((2 * i : ℕ) : ℝ) ^ 2) +
          (((2 * i : ℕ) : ℝ) ^ 2))) :
    apNormalizedVaughanActualCollectedShellMeanOn N u v k l
        ((productionConductorBlockGeometry N Q C hR).cell i) ≤
      (1 / (i : ℝ)) *
        ((1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
          (primitiveBilinearQFactor (2 * i) *
            Real.sqrt (27 * (H + 1) *
              Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) *
            ((N : ℝ) + (((2 * i : ℕ) : ℝ) ^ 2) * Real.sqrt N)) +
        (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
          vaughanTypeIIRectangularL1exp N k l *
            weightedPrimitiveFamilyMass
              ((productionConductorBlockGeometry N Q C hR).cell i)) := by
  exact apNormalizedVaughanActualCollectedShellMeanOn_cell_le_aspectGate
    N Q C u v k l i H (productionConductorBlockGeometry N Q C hR) hi
      (productionConductorBlockGeometry_cell_subset_Ioc N Q C hR i)
      hN hactive hH hAspect

/-- Finite conductor-cell/canonical-shell pairs on which the literal local
aspect hypothesis holds. -/
def vaughanAspectSafeCellShells
    (N Q C u v : ℕ) (H : ℝ) (G : ProductionConductorBlockGeometry N Q C) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (G.index ×ˢ vaughanTypeIIActiveCanonicalRectangles N u v).filter fun ikl =>
    (vaughanTypeIIRectangularD ikl.2.1 : ℝ) +
        (vaughanTypeIIRectangularX N ikl.2.1 : ℝ) ≤
      H * (((N : ℝ) / ((2 * ikl.1 : ℕ) : ℝ) ^ 2) +
        (((2 * ikl.1 : ℕ) : ℝ) ^ 2))

/-- Literal finite complement of the safe pairs.  No analytic or "extreme"
claim is attached to this compiler-defined residual family. -/
def vaughanAspectResidualCellShells
    (N Q C u v : ℕ) (H : ℝ) (G : ProductionConductorBlockGeometry N Q C) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (G.index ×ˢ vaughanTypeIIActiveCanonicalRectangles N u v).filter fun ikl =>
    ¬ ((vaughanTypeIIRectangularD ikl.2.1 : ℝ) +
        (vaughanTypeIIRectangularX N ikl.2.1 : ℝ) ≤
      H * (((N : ℝ) / ((2 * ikl.1 : ℕ) : ℝ) ^ 2) +
        (((2 * ikl.1 : ℕ) : ℝ) ^ 2)))

@[simp] theorem mem_vaughanAspectSafeCellShells
    {N Q C u v : ℕ} {H : ℝ} {G : ProductionConductorBlockGeometry N Q C}
    {ikl : ℕ × (ℕ × ℕ)} :
    ikl ∈ vaughanAspectSafeCellShells N Q C u v H G ↔
      ikl.1 ∈ G.index ∧
      ikl.2 ∈ vaughanTypeIIActiveCanonicalRectangles N u v ∧
      (vaughanTypeIIRectangularD ikl.2.1 : ℝ) +
          (vaughanTypeIIRectangularX N ikl.2.1 : ℝ) ≤
        H * (((N : ℝ) / ((2 * ikl.1 : ℕ) : ℝ) ^ 2) +
          (((2 * ikl.1 : ℕ) : ℝ) ^ 2)) := by
  rw [vaughanAspectSafeCellShells, Finset.mem_filter, Finset.mem_product]
  tauto

@[simp] theorem mem_vaughanAspectResidualCellShells
    {N Q C u v : ℕ} {H : ℝ} {G : ProductionConductorBlockGeometry N Q C}
    {ikl : ℕ × (ℕ × ℕ)} :
    ikl ∈ vaughanAspectResidualCellShells N Q C u v H G ↔
      ikl.1 ∈ G.index ∧
      ikl.2 ∈ vaughanTypeIIActiveCanonicalRectangles N u v ∧
      ¬ ((vaughanTypeIIRectangularD ikl.2.1 : ℝ) +
          (vaughanTypeIIRectangularX N ikl.2.1 : ℝ) ≤
        H * (((N : ℝ) / ((2 * ikl.1 : ℕ) : ℝ) ^ 2) +
          (((2 * ikl.1 : ℕ) : ℝ) ^ 2))) := by
  rw [vaughanAspectResidualCellShells, Finset.mem_filter, Finset.mem_product]
  tauto

/-- The safe and residual filters partition exactly the finite cell-shell
compiler family. -/
theorem vaughanAspectSafe_union_residualCellShells
    (N Q C u v : ℕ) (H : ℝ) (G : ProductionConductorBlockGeometry N Q C) :
    vaughanAspectSafeCellShells N Q C u v H G ∪
        vaughanAspectResidualCellShells N Q C u v H G =
      G.index ×ˢ vaughanTypeIIActiveCanonicalRectangles N u v := by
  simp only [vaughanAspectSafeCellShells, vaughanAspectResidualCellShells,
    Finset.filter_union_right, or_not, Finset.filter_true]

/-- The two finite compiler filters are disjoint. -/
theorem disjoint_vaughanAspectSafe_residualCellShells
    (N Q C u v : ℕ) (H : ℝ) (G : ProductionConductorBlockGeometry N Q C) :
    Disjoint (vaughanAspectSafeCellShells N Q C u v H G)
      (vaughanAspectResidualCellShells N Q C u v H G) := by
  exact Finset.disjoint_filter_filter_not _ _ _

end
end AnalyticNumberTheory.LargeSieve
