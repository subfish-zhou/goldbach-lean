import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitTupleLogs

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real HighNonunitLegal LiLiuPrereqBuchstab
open scoped Classical

theorem tupleList_pairwise {N : ℕ} {a b c e f : ℝ} {cs : List ℕ} {t : PrimeTuple}
    (ht : t ∈ primeTuples N a b c e f cs) : (tupleList t).Pairwise (· < ·) := by
  obtain ⟨_, _, _, hpre, hq⟩ := mem_primeTuples.mp ht
  have hh := List.pairwise_append.mp hpre.1
  rw [tupleList, show t.1 ++ [t.2.1, t.2.2] = (t.1 ++ [t.2.1]) ++ [t.2.2] by simp]
  apply List.pairwise_append.mpr
  refine ⟨hpre.1, by simp, ?_⟩
  intro r hr q hq'
  have he : q = t.2.2 := by simpa using hq'
  subst q
  rcases List.mem_append.mp hr with hr | hr
  · exact (hh.2.2 r hr _ (by simp)).trans hq.2.1
  · have he : r = t.2.1 := by simpa using hr
    simpa only [he] using hq.2.1

theorem tupleCubeEmbedding_monotone {m : ℕ} {R : ℝ} (hR : 1 < R)
    (S : Finset PrimeTuple) (hlen : ∀ t ∈ S, (tupleList t).length = m)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R)
    (t : S) (hord : (tupleList t.val).Pairwise (· < ·)) :
    Monotone (gridCoordinates R (tupleCubeEmbedding S hlen hmem t)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · have hi : i.val < (tupleList t.val).length := by rw [hlen _ t.property]; exact i.isLt
    have hj : j.val < (tupleList t.val).length := by rw [hlen _ t.property]; exact j.isLt
    have ho := (List.pairwise_iff_getElem.mp hord) i.val j.val hi hj hij
    have hz : 0 < (tupleCoordinates m t.val i : ℝ) := by
      have hp := ((mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mp
        ((tupleCubeEmbedding S hlen hmem t i).property)).1
      exact_mod_cast hp.pos
    simp only [tupleCubeEmbedding_coordinate]
    apply div_le_div_of_nonneg_right _ (log_pos hR).le
    apply log_le_log hz
    exact_mod_cast (show tupleCoordinates m t.val i ≤ tupleCoordinates m t.val j from by
      simpa only [tupleCoordinates, List.getD_eq_getElem _ _ hi,
        List.getD_eq_getElem _ _ hj] using ho.le)
  · exact le_rfl

theorem log_coordinate_lower {R a : ℝ} {q : ℕ} (hR : 1 < R)
    (hq : R^a ≤ (q : ℝ)) : a ≤ log (q : ℝ)/log R := by
  apply (le_div_iff₀ (log_pos hR)).mpr
  have h := log_le_log (rpow_pos_of_pos (lt_trans zero_lt_one hR) _) hq
  simpa only [log_rpow (lt_trans zero_lt_one hR)] using h

theorem log_coordinate_upper {R a : ℝ} {q : ℕ} (hR : 1 < R)
    (hq0 : 0 < q) (hq : (q : ℝ) ≤ R^a) : log (q : ℝ)/log R ≤ a := by
  apply (div_le_iff₀ (log_pos hR)).mpr
  have h := log_le_log (by exact_mod_cast hq0 : (0 : ℝ) < q) hq
  simpa only [log_rpow (lt_trans zero_lt_one hR)] using h

theorem tuple_last {m : ℕ} {t : PrimeTuple} (hlen : (tupleList t).length = m+2) :
    tupleCoordinates (m+2) t (Fin.last (m+1)) = t.2.2 := by
  have hpre : t.1.length = m := by
    simp only [tupleList, List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  simp [tupleCoordinates, tupleList, hpre]

theorem actual_tuple_colours20 {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    {t : PrimeTuple} (ht : t ∈ actualPrimeTuples N δ p false d) :
    wuLocalCutoff N δ d p.kappa2 ≤ (tupleCoordinates 5 t 0 : ℝ) ∧
    (tupleCoordinates 5 t 0 : ℝ) < wuLocalCutoff N δ d p.kappa3 ∧
    wuLocalCutoff N δ d p.kappa3 ≤ (tupleCoordinates 5 t 1 : ℝ) := by
  have h := mem_primeTuples.mp ht
  have hlen := ((secondFunctionalMother_tuple_mem _ _ _).mp h.1).1
  change t.1.length = 3 at hlen
  obtain ⟨r,s,u,he⟩ := List.length_eq_three.mp hlen
  have hc := h.2.2.2.1.2
  have hc' : secondFunctionalMotherColour (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3) r = 2 ∧
    secondFunctionalMotherColour (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3) s = 3 := by
    simp only [he, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      word, HighUnitSource.word20] at hc
    simp at hc
    exact ⟨hc.1, hc.2.1⟩
  simpa [tupleCoordinates, tupleList, he] using
    And.intro (HighUnitSource.colour_two hc'.1).1
      ⟨(HighUnitSource.colour_two hc'.1).2, HighUnitSource.colour_three hc'.2⟩

theorem actual_tuple_colours21 {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    {t : PrimeTuple} (ht : t ∈ actualPrimeTuples N δ p true d) :
    wuLocalCutoff N δ d p.kappa3 ≤ (tupleCoordinates 6 t 0 : ℝ) := by
  have h := mem_primeTuples.mp ht
  have hlen := ((secondFunctionalMother_tuple_mem _ _ _).mp h.1).1
  change t.1.length = 4 at hlen
  obtain ⟨r,s,u,v,he⟩ := List.length_eq_four.mp hlen
  have hc := h.2.2.2.1.2
  have hc' : secondFunctionalMotherColour (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3) r = 3 := by
    simp [he, word, HighUnitSource.word21] at hc
    exact hc.1
  simpa [tupleCoordinates, tupleList, he] using HighUnitSource.colour_three hc'

theorem tuple_embedding_D20 {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    (hR : 1 < (N : ℝ)^(1/2-δ)/d)
    (S : Finset PrimeTuple) (hlen : ∀ t ∈ S, (tupleList t).length = 5)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d))
    (t : S) (ht : t.val ∈ actualPrimeTuples N δ p false d)
    (hl : gridCoordinates _ (tupleCubeEmbedding S hlen hmem t) ∈ legal 3 (omega3XPhi N d δ)) :
    gridCoordinates _ (tupleCubeEmbedding S hlen hmem t) ∈
      D20 (1/p.kappa2) (1/p.kappa3) (1/p.s) (omega3XPhi N d δ) := by
  have hc := actual_tuple_colours20 ht
  have hq := (mem_primeTuples.mp ht).2.2.2.2
  refine ⟨⟨?_, ?_, ?_, tupleCubeEmbedding_monotone hR S hlen hmem t (tupleList_pairwise ht), ?_⟩, hl⟩
  · exact log_coordinate_lower hR hc.1
  · apply log_coordinate_upper hR _ hc.2.1.le
    have hpos := lt_of_lt_of_le (rpow_pos_of_pos (lt_trans zero_lt_one hR) _) hc.1
    exact_mod_cast hpos
  · exact log_coordinate_lower hR hc.2.2
  · have he : tupleCoordinates 5 t.val 4 = t.val.2.2 := tuple_last (m := 3) (hlen _ t.property)
    rw [tupleCubeEmbedding_coordinate, he]
    exact log_coordinate_upper hR hq.1.pos hq.2.2.2

theorem tuple_embedding_D21 {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    (hR : 1 < (N : ℝ)^(1/2-δ)/d)
    (S : Finset PrimeTuple) (hlen : ∀ t ∈ S, (tupleList t).length = 6)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d))
    (t : S) (ht : t.val ∈ actualPrimeTuples N δ p true d)
    (hl : gridCoordinates _ (tupleCubeEmbedding S hlen hmem t) ∈ legal 4 (omega3XPhi N d δ)) :
    gridCoordinates _ (tupleCubeEmbedding S hlen hmem t) ∈
      D21 (1/p.kappa3) (1/p.s) (omega3XPhi N d δ) := by
  have hc := actual_tuple_colours21 ht
  have hq := (mem_primeTuples.mp ht).2.2.2.2
  refine ⟨⟨log_coordinate_lower hR hc,
    tupleCubeEmbedding_monotone hR S hlen hmem t (tupleList_pairwise ht), ?_⟩, hl⟩
  have he : tupleCoordinates 6 t.val 5 = t.val.2.2 := tuple_last (m := 4) (hlen _ t.property)
  rw [tupleCubeEmbedding_coordinate, he]
  exact log_coordinate_upper hR hq.1.pos hq.2.2.2

end Wu2008DoubleSieve.HighNonunit
