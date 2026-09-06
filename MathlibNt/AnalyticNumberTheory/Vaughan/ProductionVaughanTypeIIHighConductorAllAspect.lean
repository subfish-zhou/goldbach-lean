import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIAllAspectBlockScalar

/-!
# Full Vaughan Type-II mean on the production high-conductor cells

This checker-facing leaf keeps the literal conductor carrier throughout.  It
first repeats the exact full-to-active-collected-shell decomposition on an
arbitrary finite conductor set, applies the all-aspect scalar theorem cell by
cell, and finally reindexes the production high-conductor set through the
pairwise disjoint canonical conductor geometry.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section
set_option maxHeartbeats 1600000

/-- The full AP-normalized Vaughan Type-II mean on exactly the finite conductor
set `S`. -/
def apNormalizedVaughanTypeIIMeanOn
    (N u v : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      primitivePrefixAmplitude
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ

/-- The global exact shell decomposition restricts to an arbitrary conductor
set without enlarging that carrier. -/
theorem apNormalizedVaughanTypeIIMeanOn_le_active_collected_shells
    (N u v : ℕ) (S : Finset ℕ) :
    apNormalizedVaughanTypeIIMeanOn N u v S ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        apNormalizedVaughanActualCollectedShellMeanOn
          N u v kl.1 kl.2 S := by
  unfold apNormalizedVaughanTypeIIMeanOn
    apNormalizedVaughanActualCollectedShellMeanOn
  calc
    _ ≤ ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q,
          ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
              N u v kl.1 kl.2 q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun χ _ =>
          primitivePrefixAmplitude_vaughanTypeII_le_active_collected_shells
            N u v q χ
      · positivity
    _ = ∑ q ∈ S,
        ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
          ((q.totient : ℝ)⁻¹) *
            ∑ χ : PrimitiveCharacter q,
              Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
                N u v kl.1 kl.2 q χ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm]

/-- A complete production cell, with its literal full Vaughan Type-II
coefficient, satisfies the all-aspect scalar estimate. -/
theorem apNormalizedVaughanTypeIIMeanOn_productionCell_le_allAspect
    (N Q C u v i : ℕ) (G : ProductionConductorBlockGeometry N Q C)
    (hiG : i ∈ G.index) (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N)
    (hu : u < N) (hv : v < N) :
    apNormalizedVaughanTypeIIMeanOn N u v (G.cell i) ≤
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
          ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
            (N : ℝ) / Real.sqrt (v + 1 : ℕ) +
            (i : ℝ) * Real.sqrt N)) := by
  exact (apNormalizedVaughanTypeIIMeanOn_le_active_collected_shells
    N u v (G.cell i)).trans
      (sum_activeRectangles_cell_le_card_mul_allAspect_scalar
        N Q C u v i G hiG hcell hN hi h2i hu hv)

/-- The genuine aggregate over the exact production high-conductor carrier.
The reciprocal and ordinary lower-endpoint sums are paid by the two geometry
ledgers; the middle two all-aspect terms retain the concrete index cardinality. -/
theorem apNormalizedVaughanTypeIIMeanOn_highConductor_le_allAspect_aggregate
    (N Q C u v : ℕ)
    (hN : 9 ≤ N)
    (hR : 0 < logConductorThreshold N C)
    (hQ : Q ≤ N / 2)
    (hu : u < N) (hv : v < N) :
    apNormalizedVaughanTypeIIMeanOn N u v (highConductorSet N Q C) ≤
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15) *
          (2 * (N : ℝ) / logConductorThreshold N C +
            (((productionConductorBlockGeometry N Q C hR).index.card : ℕ) : ℝ) *
              ((N : ℝ) / Real.sqrt (u + 1 : ℕ) +
                (N : ℝ) / Real.sqrt (v + 1 : ℕ)) +
            2 * (Q : ℝ) * Real.sqrt N) := by
  let G := productionConductorBlockGeometry N Q C hR
  let A : ℝ := ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ)
  let K : ℝ := 1000000 * Real.log (4 * N + 4 : ℕ) ^ 15
  let U : ℝ := (N : ℝ) / Real.sqrt (u + 1 : ℕ)
  let V : ℝ := (N : ℝ) / Real.sqrt (v + 1 : ℕ)
  let R : ℝ := logConductorThreshold N C
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAK0 : 0 ≤ A * K := mul_nonneg hA0 hK0
  have hQ2 : 2 * Q ≤ N := by omega
  -- Empty cells contribute zero; an occupied cell supplies the upper-endpoint bound.
  have hcell (i : ℕ) (hi : i ∈ G.index) :
      apNormalizedVaughanTypeIIMeanOn N u v (G.cell i) ≤
        A * K * ((N : ℝ) / i + U + V + (i : ℝ) * Real.sqrt N) := by
    by_cases hempty : G.cell i = ∅
    · simp only [hempty, apNormalizedVaughanTypeIIMeanOn, Finset.sum_empty]
      exact mul_nonneg hAK0 (by positivity)
    · obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hIoc : G.cell i ⊆ Finset.Ioc i (2 * i) := by
        dsimp [G]
        exact productionConductorBlockGeometry_cell_subset_Ioc N Q C hR i
      have hiq : i < q := (Finset.mem_Ioc.mp (hIoc hq)).1
      have hqHigh : q ∈ highConductorSet N Q C := by
        rw [← G.cover]
        exact Finset.mem_biUnion.mpr ⟨i, hi, hq⟩
      have hqQ : q ≤ Q :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hqHigh).1).2
      have h2i : 2 * i ≤ N := by omega
      convert
        apNormalizedVaughanTypeIIMeanOn_productionCell_le_allAspect
          N Q C u v i G hi hIoc hN (G.lower_pos i hi) h2i hu hv using 1 <;>
        dsimp [A, K, U, V] <;> ring
  -- Reindex the exact high-conductor carrier, without adding conductors.
  have hreindex :
      apNormalizedVaughanTypeIIMeanOn N u v (highConductorSet N Q C) =
        ∑ i ∈ G.index,
          apNormalizedVaughanTypeIIMeanOn N u v (G.cell i) := by
    unfold apNormalizedVaughanTypeIIMeanOn
    rw [← G.cover, Finset.sum_biUnion G.pairwise]
  rw [hreindex]
  calc
    _ ≤ ∑ i ∈ G.index,
        A * K * ((N : ℝ) / i + U + V + (i : ℝ) * Real.sqrt N) := by
      exact Finset.sum_le_sum fun i hi => hcell i hi
    _ = A * K *
        ((N : ℝ) * (∑ i ∈ G.index, ((i : ℝ)⁻¹)) +
          (G.index.card : ℝ) * (U + V) +
          (∑ i ∈ G.index, (i : ℝ)) * Real.sqrt N) := by
      calc
        _ = A * K * (∑ i ∈ G.index,
            ((N : ℝ) / i + U + V + (i : ℝ) * Real.sqrt N)) := by
              rw [Finset.mul_sum]
        _ = _ := by
          simp only [div_eq_mul_inv, Finset.sum_add_distrib,
            Finset.sum_const, nsmul_eq_mul]
          push_cast
          rw [← Finset.mul_sum, ← Finset.sum_mul]
          ring
    _ ≤ A * K *
        ((N : ℝ) * (2 / R) + (G.index.card : ℝ) * (U + V) +
          (2 * (Q : ℝ)) * Real.sqrt N) := by
      apply mul_le_mul_of_nonneg_left _ hAK0
      have hinv : (∑ i ∈ G.index, ((i : ℝ)⁻¹)) ≤ 2 / R := by
        simpa [G, R] using G.inv_lower_sum_le
      have hsum : (∑ i ∈ G.index, (i : ℝ)) ≤ 2 * (Q : ℝ) := G.lower_sum_le
      -- Only the endpoint sums change; the two middle terms keep the index cardinality.
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg N)) le_rfl)
        (mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg N))
    _ = ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15) *
          (2 * (N : ℝ) / logConductorThreshold N C +
            (((productionConductorBlockGeometry N Q C hR).index.card : ℕ) : ℝ) *
              ((N : ℝ) / Real.sqrt (u + 1 : ℕ) +
                (N : ℝ) / Real.sqrt (v + 1 : ℕ)) +
            2 * (Q : ℝ) * Real.sqrt N) := by
      dsimp [A, K, U, V, R, G]
      ring

end
end AnalyticNumberTheory.LargeSieve
