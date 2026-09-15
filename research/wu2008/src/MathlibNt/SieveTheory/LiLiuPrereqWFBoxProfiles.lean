import MathlibNt.SieveTheory.LiLiuPrereqWFSignedRounding

/-!
# Occurrence-preserving canonical box profiles

Profiles are sorted multisets of labels, not sets of labels. Distinct prime
sets with the same multiplicities give the same profile.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset LiLiuPrereqWFAdmissibility
open scoped Classical

noncomputable def boxProfile (label : ℕ → ℕ) (S : Finset ℕ) : List ℕ :=
  (S.val.map label).sort (· ≥ ·)

@[simp]
theorem boxProfile_length (label : ℕ → ℕ) (S : Finset ℕ) :
    (boxProfile label S).length = S.card := by
  simp [boxProfile]

@[simp]
theorem mem_boxProfile (label : ℕ → ℕ) (S : Finset ℕ) (j : ℕ) :
    j ∈ boxProfile label S ↔ ∃ p ∈ S, label p = j := by
  simp [boxProfile]

theorem boxProfile_count (label : ℕ → ℕ) (S : Finset ℕ) (j : ℕ) :
    (boxProfile label S).count j = (S.filter (fun p => label p = j)).card := by
  have h := congrArg (Multiset.count j) (Multiset.sort_eq (S.val.map label) (· ≥ ·))
  simpa only [Multiset.coe_count, Multiset.count_map, Finset.card,
    Finset.filter_val, boxProfile, eq_comm] using h

theorem boxProfile_pairwise (label : ℕ → ℕ) (S : Finset ℕ) :
    (boxProfile label S).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

theorem boxProfile_eq_of_counts {label : ℕ → ℕ} {S T : Finset ℕ}
    (h : ∀ j, (boxProfile label S).count j = (boxProfile label T).count j) :
    boxProfile label S = boxProfile label T :=
  (List.perm_iff_count.mpr h).eq_of_pairwise'
    (boxProfile_pairwise label S) (boxProfile_pairwise label T)

/-- The prime order gives exactly the same occurrence list whenever the
labels respect that order. Equal labels are retained, not collapsed. -/
theorem boxProfile_eq_map_sort (label : ℕ → ℕ) (S : Finset ℕ)
    (hmono : ∀ p ∈ S, ∀ q ∈ S, p ≤ q → label p ≤ label q) :
    boxProfile label S = (S.sort (· ≥ ·)).map label := by
  apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
  · exact boxProfile_pairwise label S
  · rw [List.pairwise_map]
    apply (S.pairwise_sort (· ≥ ·)).imp_of_mem
    intro p q hp hq hpq
    exact hmono q ((Finset.mem_sort _).mp hq) p ((Finset.mem_sort _).mp hp) hpq
  · apply Multiset.coe_eq_coe.mp
    change ↑(boxProfile label S) = Multiset.map label (↑(S.sort (· ≥ ·)) : Multiset ℕ)
    rw [boxProfile, Multiset.sort_eq, Finset.sort_eq]

theorem boxProfile_nodup_iff (label : ℕ → ℕ) (S : Finset ℕ) :
    (boxProfile label S).Nodup ↔ Set.InjOn label (↑S : Set ℕ) := by
  change Multiset.Nodup (↑(boxProfile label S) : Multiset ℕ) ↔ _
  rw [boxProfile, Multiset.sort_eq, Finset.nodup_map_iff_injOn]

theorem boxProfile_prod (label : ℕ → ℕ) (b : ℕ → ℝ) (S : Finset ℕ) :
    ((boxProfile label S).map b).prod = ∏ p ∈ S, b (label p) := by
  change (Multiset.map b (↑(boxProfile label S) : Multiset ℕ)).prod = _
  rw [boxProfile, Multiset.sort_eq, Multiset.map_map]
  rfl

theorem cubicPrefixBound_map_iff (upper : Bool) (b : ℕ → ℝ) (D : ℝ)
    (label : ℕ → ℕ) (l : List ℕ) :
    CubicPrefixBound upper b D (l.map label) ↔
      CubicPrefixBound upper (fun p => b (label p)) D l := by
  simp only [CubicPrefixBound, List.length_map, ← List.map_take, List.map_map,
    List.getElem_map, Function.comp_def]

theorem admissible_map_iff (upper : Bool) (b : ℕ → ℝ) (D : ℝ)
    (label : ℕ → ℕ) (l : List ℕ) :
    Admissible upper b D (l.map label) ↔
      Admissible upper (fun p => b (label p)) D l := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, (cubicPrefixBound_map_iff _ _ _ _ _).mp h.cubic⟩
    · simpa using h.one_le
    · simpa using h.decreasing
    · simpa using h.head_lt_sqrt
  · intro h
    refine ⟨?_, ?_, ?_, (cubicPrefixBound_map_iff _ _ _ _ _).mpr h.cubic⟩
    · simpa using h.one_le
    · simpa using h.decreasing
    · simpa using h.head_lt_sqrt

theorem roundedSupport_boxProfile_iff (upper : Bool) (label : ℕ → ℕ)
    (b : ℕ → ℝ) (D : ℝ) (S : Finset ℕ)
    (hmono : ∀ p ∈ S, ∀ q ∈ S, p ≤ q → label p ≤ label q) :
    RoundedSupport upper (fun p => b (label p)) D S ↔
      ((boxProfile label S).map b).prod < D ∧
        CubicPrefixBound upper b D (boxProfile label S) := by
  rw [RoundedSupport, boxProfile_prod, boxProfile_eq_map_sort label S hmono,
    cubicPrefixBound_map_iff, roundedSetAdmissible_iff_cubicPrefixBound]

/-- The box-count test singles out the canonical occurrence profile.
The inputs are only membership and disjointness of finite sets. -/
theorem boxProfile_matches_iff (label : ℕ → ℕ) (B : ℕ → Finset ℕ)
    (B₀ N : Finset ℕ) (t : List ℕ)
    (ht : t.Pairwise (· ≥ ·))
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hsep : ∀ j, Disjoint B₀ (B j))
    (hcover : ∀ p ∈ N \ B₀, p ∈ B (label p)) :
    (N ⊆ B₀ ∪ t.toFinset.biUnion B ∧
      (∀ j ∈ t.toFinset, (N ∩ B j).card = t.count j)) ↔
        t = boxProfile label (N \ B₀) := by
  have hfilter (j : ℕ) :
      (N \ B₀).filter (fun p => label p = j) = N ∩ B j := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hp, hj⟩
      exact ⟨hp.1, hj ▸ hcover p (Finset.mem_sdiff.mpr hp)⟩
    · rintro ⟨hp, hpj⟩
      have hp0 : p ∉ B₀ := fun h => Finset.disjoint_left.mp (hsep j) h hpj
      refine ⟨⟨hp, hp0⟩, ?_⟩
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj (label p) j hne)
        (hcover p (Finset.mem_sdiff.mpr ⟨hp, hp0⟩)) hpj
  have hcount (j : ℕ) :
      (boxProfile label (N \ B₀)).count j = (N ∩ B j).card := by
    rw [boxProfile_count, hfilter]
  constructor
  · rintro ⟨hsupport, hcounts⟩
    apply List.Perm.eq_of_pairwise' ht (boxProfile_pairwise _ _)
    apply List.perm_iff_count.mpr
    intro j
    rw [hcount]
    by_cases hj : j ∈ t.toFinset
    · exact (hcounts j hj).symm
    · have hz : N ∩ B j = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hpN, hpj⟩ := Finset.mem_inter.mp hp
        have hp0 : p ∉ B₀ := fun h => Finset.disjoint_left.mp (hsep j) h hpj
        obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp
          ((Finset.mem_union.mp (hsupport hpN)).resolve_left hp0)
        exact Finset.disjoint_left.mp (hdisj i j (by rintro rfl; exact hj hi)) hpi hpj
      rw [hz, Finset.card_empty]
      exact List.count_eq_zero.mpr (fun h => hj (List.mem_toFinset.mpr h))
  · rintro rfl
    refine ⟨?_, fun j _ => (hcount j).symm⟩
    intro p hp
    by_cases hp0 : p ∈ B₀
    · exact Finset.mem_union_left _ hp0
    · have hpS := Finset.mem_sdiff.mpr ⟨hp, hp0⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨label p, List.mem_toFinset.mpr ((mem_boxProfile _ _ _).mpr ⟨p, hpS, rfl⟩),
          hcover p hpS⟩)

#check boxProfile_eq_of_counts
#check roundedSupport_boxProfile_iff
#check boxProfile_matches_iff
#print axioms boxProfile_eq_of_counts
#print axioms roundedSupport_boxProfile_iff
#print axioms boxProfile_matches_iff

end MathlibNt.SieveTheory.LiLiuPrereqWF
