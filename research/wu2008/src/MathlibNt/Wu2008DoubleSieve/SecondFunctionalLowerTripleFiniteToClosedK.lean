import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleTupleGeometry

namespace Wu2008DoubleSieve.LowerTripleGroupedFinite
open Finset Real HighNonunitLegal LiLiuPrereqBuchstab
open scoped Classical

theorem closedPrimeK_sum (R phi : ℝ) (D : Set (Fin 3 → ℝ)) :
    LowerTripleContinuous.closedPrimeK D R phi =
      ∑ f : Fin 3 → primeSlabPrimes R, if gridCoordinates R f ∈ D then
        primeSlabWeight R f * G 1 phi (gridCoordinates R f) else 0 := by
  unfold LowerTripleContinuous.closedPrimeK
  apply sum_congr rfl
  intro f _
  by_cases hf : gridCoordinates R f ∈ D
  · simp only [Set.indicator_of_mem hf, if_pos hf, LowerTripleContinuous.G]
  · simp only [Set.indicator_of_notMem hf, if_neg hf, mul_zero]

/-- Equality on the complete labelled image, followed only by nonnegative enlargement. -/
theorem tuple_sum_le_closed_mask {m : ℕ} {R C phi : ℝ} (hR : 1 < R) (hC : 0 ≤ C)
    (S : Finset PrimeTriple) (E : S ↪ (Fin m → primeSlabPrimes R))
    (j : Fin m) (D : Set (Fin m → ℝ)) (F : PrimeTriple → ℝ)
    (hD : ∀ t : S, gridCoordinates R (E t) ∈ D)
    (hF : ∀ t : S, F t.val = C * primeSlabWeight R (E t) * G j phi (gridCoordinates R (E t))) :
    (∑ t ∈ S, F t) ≤ C * ∑ f : Fin m → primeSlabPrimes R,
      if gridCoordinates R f ∈ D then primeSlabWeight R f * G j phi (gridCoordinates R f) else 0 := by
  let w := fun f : Fin m → primeSlabPrimes R =>
    C * (if gridCoordinates R f ∈ D then primeSlabWeight R f * G j phi (gridCoordinates R f) else 0)
  have hw (f : Fin m → primeSlabPrimes R) : 0 ≤ w f := by
    dsimp only [w]
    split_ifs
    · exact mul_nonneg hC (mul_nonneg (by unfold primeSlabWeight; positivity)
        (G_bounds j phi (gridCoordinates_mem hR f)).1)
    · exact mul_nonneg hC le_rfl
  have he : (∑ f ∈ univ.image E, w f) = ∑ t ∈ S, F t := by
    rw [sum_image (fun a _ b _ h => E.injective h)]
    calc
      _ = ∑ t : S, F t.val := by
        apply sum_congr rfl
        intro t _
        dsimp only [w]
        rw [if_pos (hD t), hF t]
        ring
      _ = _ := sum_coe_sort S F
  have hle := sum_le_sum_of_subset_of_nonneg (subset_univ (univ.image E))
    (fun f _ _ => hw f)
  rw [he] at hle
  simpa only [w, mul_sum] using hle

theorem filtered_inner_le_closedPrimeKj {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    (∑ t ∈ (legalPrimeTriples N δ p j d).filter
      (fun t => (LowerTripleGrouped.actualBands N δ p j d).2.2.2.2.1 ≤ (t.2.2 : ℝ)),
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1) ≤
    ((N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d))) *
      LowerTripleContinuous.closedPrimeKj ((N : ℝ)^(1/2-δ)/d)
        (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j (omega3XPhi N d δ) := by
  have hd0 : 0 < d := boxConvolutionSupport_pos
    (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
  have hbds := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hR := hbds.2.1
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hpos : 0 ≤ 2*δ/(1/2-δ) := div_nonneg (by positivity) (by linarith)
    linarith [hbds.2.2.1]
  let S := (legalPrimeTriples N δ p j d).filter
    (fun t => (LowerTripleGrouped.actualBands N δ p j d).2.2.2.2.1 ≤ (t.2.2 : ℝ))
  have hactual (t : S) : t.val ∈ actualPrimeTriples N δ p j d :=
    (mem_filter.mp (mem_filter.mp t.property).1).1
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d) :=
    fun t ht => actual_tuple_cube (by omega) hδ hδhi hb p hp hs hd (hactual ⟨t,ht⟩)
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have hh := tupleProduct_pos hd0 (hactual t)
    rw [tupleProduct_literal] at hh
    by_contra hn
    have he := Nat.eq_zero_of_not_pos hn
    simp only [he, mul_zero, lt_self_iff_false] at hh
  have hprime (t : S) : 1 < t.val.2.1 :=
    (mem_primeWindow.mp (mem_primeTriples.mp (hactual t)).2.1).1.one_lt
  have hscale : 0 ≤ (N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d)) :=
    div_nonneg (Nat.cast_nonneg N) (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)
  unfold LowerTripleContinuous.closedPrimeKj
  rw [closedPrimeK_sum]
  apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hmem) 1
  · intro t
    exact tuple_embedding_closed_domain hR S hmem t j (hactual t) (mem_filter.mp t.property).2
  · intro t
    exact tupleCubeEmbedding_kernel (by omega) hd0 hR hphi S hmem t (hprod t) (hprime t)

/-- The full original sigma is retained, with no transport or mask hypothesis. -/
theorem filtered_finiteBuchstabMain_le_closedPrimeKj {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6) :
    (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * (∑ t ∈ (legalPrimeTriples N δ p j d).filter
      (fun t => (LowerTripleGrouped.actualBands N δ p j d).2.2.2.2.1 ≤ (t.2.2 : ℝ)),
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1)) ≤
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * ((N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d))) *
      LowerTripleContinuous.closedPrimeKj ((N : ℝ)^(1/2-δ)/d)
        (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j (omega3XPhi N d δ) := by
  apply sum_le_sum
  intro d hd
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (filtered_inner_le_closedPrimeKj hN hδ hδhi hb p hp hs j hd)
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))

/-- All six independent closed atoms, without union or product-image deduplication. -/
theorem filtered_finiteBuchstabMain_all6_le_closedPrimeKj {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    (∑ j : Fin 6, ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * (∑ t ∈ (legalPrimeTriples N δ p j d).filter
      (fun t => (LowerTripleGrouped.actualBands N δ p j d).2.2.2.2.1 ≤ (t.2.2 : ℝ)),
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1)) ≤
    ∑ j : Fin 6, ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * ((N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d))) *
      LowerTripleContinuous.closedPrimeKj ((N : ℝ)^(1/2-δ)/d)
        (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j (omega3XPhi N d δ) := by
  exact sum_le_sum (fun j _ => filtered_finiteBuchstabMain_le_closedPrimeKj hN hδ hδhi hb p hp hs j)

end Wu2008DoubleSieve.LowerTripleGroupedFinite
