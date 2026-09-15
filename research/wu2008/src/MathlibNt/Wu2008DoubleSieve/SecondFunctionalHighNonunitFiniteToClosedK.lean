import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitTupleGeometry

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real HighNonunitLegal LiLiuPrereqBuchstab
open scoped Classical

/-- Transport only the Fintype dictionary, never the function carrier. -/
theorem finiteTransport_sum_fintype_congr {A : Type*} (I J : Fintype A)
    (f g : A → ℝ) (h : ∀ a, f a = g a) :
    @Finset.sum A ℝ _ (@Finset.univ A I) f = @Finset.sum A ℝ _ (@Finset.univ A J) g := by
  have he : I = J := Subsingleton.elim _ _
  subst J
  exact sum_congr rfl (fun a _ => h a)

theorem finiteTransport_closed20 (R a2 a3 b phi : ℝ) :
    closedPrimeK20 R a2 a3 b phi =
      ∑ f : Fin 5 → primeSlabPrimes R, if gridCoordinates R f ∈ D20 a2 a3 b phi then
        primeSlabWeight R f * G 3 phi (gridCoordinates R f) else 0 := by
  unfold closedPrimeK20
  apply finiteTransport_sum_fintype_congr
  intro f
  split_ifs <;> rfl

theorem finiteTransport_closed21 (R a3 b phi : ℝ) :
    closedPrimeK21 R a3 b phi =
      ∑ f : Fin 6 → primeSlabPrimes R, if gridCoordinates R f ∈ D21 a3 b phi then
        primeSlabWeight R f * G 4 phi (gridCoordinates R f) else 0 := by
  unfold closedPrimeK21
  apply finiteTransport_sum_fintype_congr
  intro f
  split_ifs <;> rfl

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
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (high : Bool)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    (∑ t ∈ legalPrimeTuples N δ p high d,
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1) ≤
      ((N : ℝ)/d/log ((N : ℝ)^(1/2-δ)/d)) * sourceClosedK N d δ p high := by
  have hd0 : 0 < d := boxConvolutionSupport_pos
    (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
  have hR := (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
  let S := legalPrimeTuples N δ p high d
  have hlen : ∀ t ∈ S, (tupleList t).length = if high then 6 else 5 :=
    fun t ht => high_tuple_length high (mem_filter.mp ht).1
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d) :=
    fun t ht => actual_tuple_cube (by omega) hδ hδhi hb p hp hs hd (mem_filter.mp ht).1
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have hh := tupleProduct_pos hd0 (mem_filter.mp t.property).1
    by_contra hz
    have he := Nat.eq_zero_of_not_pos hz
    simp only [tupleProduct, he, mul_zero, lt_self_iff_false] at hh
  have hprime (t : S) : 1 < t.val.2.1 :=
    (mem_primeWindow.mp (mem_primeTuples.mp (mem_filter.mp t.property).1).2.1).1.one_lt
  have hgate (t : S) : tupleProduct d t.val * t.val.2.1 ≤ N := (mem_filter.mp t.property).2
  have hscale : 0 ≤ (N : ℝ)/d/log ((N : ℝ)^(1/2-δ)/d) :=
    div_nonneg (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)) (log_pos hR).le
  cases high with
  | false =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 3) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * closedPrimeK20 _ _ _ _ _
    rw [finiteTransport_closed20]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 3
    · intro t
      exact tuple_embedding_D20 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2
  | true =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 4) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * closedPrimeK21 _ _ _ _
    rw [finiteTransport_closed21]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 4
    · intro t
      exact tuple_embedding_D21 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2

/-- Original copN source and original sigma; no positivity of its total mass is required. -/
theorem finiteBuchstabMain_le_sourceClosedKMass {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (high : Bool) :
    finiteBuchstabMain N δ Δ V p high ≤ sourceClosedKMass N δ Δ V p high := by
  unfold finiteBuchstabMain sourceClosedKMass
  apply sum_le_sum
  intro d hd
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (finite_inner_le_sourceClosedK hN hδ hδhi hb p hp hs high hd)
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))

theorem finiteBuchstabMain_pair_le_sourceClosedKMass {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    finiteBuchstabMain N δ Δ V p false + finiteBuchstabMain N δ Δ V p true ≤
      sourceClosedKMass N δ Δ V p false + sourceClosedKMass N δ Δ V p true :=
  add_le_add (finiteBuchstabMain_le_sourceClosedKMass hN hδ hδhi hb p hp hs false)
    (finiteBuchstabMain_le_sourceClosedKMass hN hδ hδhi hb p hp hs true)

end Wu2008DoubleSieve.HighNonunit
