import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeTupleGeometry

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real HighNonunitLegal LiLiuPrereqBuchstab
open scoped Classical

theorem closedK_domain (R b c e f phi : ℝ) (j : Fin 4) :
    closedK R b c e f phi j =
      FourPrimeContinuous.closedPrimeK (closedDomain b c e f j) R phi := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))) j <;> rfl

theorem finiteTransport_closed (R phi : ℝ) (D : Set (Fin 4 → ℝ)) :
    FourPrimeContinuous.closedPrimeK D R phi =
      ∑ f : Fin 4 → primeSlabPrimes R, if gridCoordinates R f ∈ D then
        primeSlabWeight R f * G 2 phi (gridCoordinates R f) else 0 := by
  unfold FourPrimeContinuous.closedPrimeK
  apply HighNonunit.finiteTransport_sum_fintype_congr
  intro f
  by_cases hf : gridCoordinates R f ∈ D
  · simp only [Set.indicator_of_mem hf, if_pos hf, FourPrimeContinuous.G]
  · simp only [Set.indicator_of_notMem hf, if_neg hf, mul_zero]

/-- Equality on the complete labelled image, followed only by nonnegative enlargement. -/
theorem tuple_sum_le_closed_mask {m : ℕ} {R C phi : ℝ} (hR : 1 < R) (hC : 0 ≤ C)
    (S : Finset PrimeTuple) (E : S ↪ (Fin m → primeSlabPrimes R))
    (j : Fin m) (D : Set (Fin m → ℝ)) (F : PrimeTuple → ℝ)
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

theorem finite_inner_le_sourceClosedK {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    (∑ t ∈ legalPrimeTuples N δ p j d,
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.1) *
        ((N : ℝ)/tupleProduct d t) / log t.1) ≤
      ((N : ℝ)/d/log ((N : ℝ)^(1/2-δ)/d)) * sourceClosedK N d δ p j := by
  have hd0 : 0 < d := boxConvolutionSupport_pos
    (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
  have hR := (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
  let S := legalPrimeTuples N δ p j d
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d) :=
    fun t ht => actual_tuple_cube (by omega) hδ hδhi hb p hp hs hd (mem_filter.mp ht).1
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have hh := tupleProduct_pos hd0 (mem_filter.mp t.property).1
    rw [tupleProduct_literal] at hh
    by_contra hn
    have he := Nat.eq_zero_of_not_pos hn
    simp only [he, mul_zero, lt_self_iff_false] at hh
  have hprime (t : S) : 1 < t.val.1 :=
    (mem_primeWindow.mp (mem_primeTuples.mp (mem_filter.mp t.property).1).1).1.one_lt
  have hgate (t : S) : tupleProduct d t.val * t.val.1 ≤ N := (mem_filter.mp t.property).2
  have hscale : 0 ≤ (N : ℝ)/d/log ((N : ℝ)^(1/2-δ)/d) :=
    div_nonneg (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)) (log_pos hR).le
  have hk (t : S) := tupleCubeEmbedding_legal_kernel (by omega) hd0 hR
    S hmem t (hprod t) (hprime t) (hgate t)
  unfold sourceClosedK
  rw [closedK_domain, finiteTransport_closed]
  apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hmem) 2
  · intro t
    exact tuple_embedding_domain hp hR S hmem t j (mem_filter.mp t.property).1
  · intro t
    exact (hk t).2.2

/-- Original sigma and all ordered labels, with the actual scale paid exactly once. -/
theorem finiteBuchstabMain_le_sourceClosedKMass {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4) :
    finiteBuchstabMain N δ Δ V p j ≤ sourceClosedKMass N δ Δ V p j := by
  unfold finiteBuchstabMain sourceClosedKMass HighSourcePayload.mass
  apply sum_le_sum
  intro d hd
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (finite_inner_le_sourceClosedK hN hδ hδhi hb p hp hs j hd)
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))

/-- All four canonical closed atoms are retained, including the zero-width boundary. -/
theorem finiteBuchstabMain_all4_le_sourceClosedKMass {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    (∑ j : Fin 4, finiteBuchstabMain N δ Δ V p j) ≤
      ∑ j : Fin 4, sourceClosedKMass N δ Δ V p j :=
  sum_le_sum (fun j _ => finiteBuchstabMain_le_sourceClosedKMass hN hδ hδhi hb p hp hs j)

end Wu2008DoubleSieve.FourPrimeNonunit
