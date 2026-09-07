import MathlibNt.SieveTheory.LiLiuPrereqWFSeparated

/-!
# Fixed multi-box weights at every real level split

The hypothesis is the explicit numerical prefix-square condition on the list
of actual prime upper bounds. Repeated labels retain their slot multiplicity.
The subsequent `LiLiuPrereqWFGeometry` and `LiLiuPrereqWFGeometricBoxes`
derive this condition with Iwaniec's geometric parameter losses. Constructing
the complete signed sieve family with its density remains a separate task.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset LiLiuPrereqWFBoxAllocation

theorem supportedAt_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ArithmeticFunction ℝ) (U : ι → ℝ)
    (hf : ∀ i ∈ s, SupportedAt (f i) (U i)) (hU : ∀ i ∈ s, 0 ≤ U i) :
    SupportedAt (∏ i ∈ s, f i) (∏ i ∈ s, U i) := by
  induction s using Finset.induction_on with
  | empty => simpa using supportedAt_one
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact supportedAt_mul (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hU j (Finset.mem_insert_of_mem hj)))
        (hU i (Finset.mem_insert_self i s))

theorem boxProduct_supportedAt {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : ι → Finset ℕ) (k : ι → ℕ) (U : ι → ℝ)
    (hU : ∀ i ∈ s, 0 ≤ U i)
    (hB : ∀ i ∈ s, ∀ p ∈ B i, p.Prime → (p : ℝ) ≤ U i) :
    SupportedAt (boxProduct s B k) (∏ i ∈ s, U i ^ k i) :=
  supportedAt_prod s _ _ (fun i hi => boxWeight_supportedAt (B i) (hU i hi) (hB i hi) _)
    (fun i hi => pow_nonneg (hU i hi) _)

theorem boxLeftProduct_supportedAt {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : ι → Finset ℕ) (a b : ι → ℕ) (U : ι → ℝ)
    (hU : ∀ i ∈ s, 0 ≤ U i)
    (hB : ∀ i ∈ s, ∀ p ∈ B i, p.Prime → (p : ℝ) ≤ U i) :
    SupportedAt (boxLeftProduct s B a b) (∏ i ∈ s, U i ^ a i) :=
  supportedAt_prod s _ _
    (fun i hi => supportedAt_smul _
      (boxWeight_supportedAt (B i) (hU i hi) (hB i hi) _))
    (fun i hi => pow_nonneg (hU i hi) _)

theorem prod_pow_list_count_of_subset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (l : List ι) (U : ι → ℝ) (hl : l.toFinset ⊆ s) :
    (∏ i ∈ s, U i ^ l.count i) = (l.map U).prod := by
  rw [Finset.prod_list_map_count]
  symm
  apply Finset.prod_subset hl
  intro i _ hi
  have hni : i ∉ l := fun h => hi (List.mem_toFinset.mpr h)
  simp [List.count_eq_zero.mpr hni]

/-- The weight and its multiplicities are fixed by input, before selecting
Q1,Q2. Only the occurrence partition and its two factors depend on the split. -/
theorem list_boxProduct_factors {ι : Type*} [DecidableEq ι]
    (input : List ι) (B : ι → Finset ℕ) (U : ι → ℝ) {Q Q₁ Q₂ : ℝ}
    (hU : ∀ i ∈ input.toFinset, 0 ≤ U i)
    (hB : ∀ i ∈ input.toFinset, ∀ p ∈ B i, p.Prime → (p : ℝ) ≤ U i)
    (hdisj : ∀ ⦃i⦄, i ∈ input.toFinset → ∀ ⦃j⦄, j ∈ input.toFinset →
      i ≠ j → Disjoint (B i) (B j))
    (hprefix : PrefixSquareBound U Q input)
    (hQ₁ : 1 ≤ Q₁) (hQ₂ : 1 ≤ Q₂) (hsplit : Q₁ * Q₂ = Q) :
    ∃ f g : ArithmeticFunction ℝ,
      BoundedOne f ∧ SupportedAt f Q₁ ∧ BoundedOne g ∧ SupportedAt g Q₂ ∧
      boxProduct input.toFinset B (fun i => input.count i) = f * g := by
  have hp : PrefixSquareBound U (Q₁ * Q₂) input := by simpa only [hsplit] using hprefix
  obtain ⟨left, right, hpart, hleft, hright⟩ :=
    exists_boxPartition_of_prefixSquareBound U hQ₁ hQ₂ input hp
  have hleftsub : left.toFinset ⊆ input.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hpart.sublists.1.subset (List.mem_toFinset.mp hi))
  have hrightsub : right.toFinset ⊆ input.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hpart.sublists.2.subset (List.mem_toFinset.mp hi))
  have hcounts : ∀ i ∈ input.toFinset, left.count i + right.count i = input.count i := by
    intro i _
    simpa only [List.count_append] using hpart.perm.count_eq i
  refine ⟨boxLeftProduct input.toFinset B left.count right.count,
    boxProduct input.toFinset B right.count,
    boxLeftProduct_boundedOne _ _ _ _ hdisj, ?_,
    boxProduct_boundedOne _ _ _ hdisj, ?_, boxProduct_split _ _ _ _ _ hcounts⟩
  · apply supportedAt_mono (boxLeftProduct_supportedAt _ _ _ _ U hU hB)
    rw [prod_pow_list_count_of_subset _ left U hleftsub]
    exact hleft
  · apply supportedAt_mono (boxProduct_supportedAt _ _ _ U hU hB)
    rw [prod_pow_list_count_of_subset _ right U hrightsub]
    exact hright

theorem list_boxProduct_wellFactorable {ι : Type*} [DecidableEq ι]
    (input : List ι) (B : ι → Finset ℕ) (U : ι → ℝ) {Q : ℝ} (hQ : 1 ≤ Q)
    (hU : ∀ i ∈ input.toFinset, 0 ≤ U i)
    (hB : ∀ i ∈ input.toFinset, ∀ p ∈ B i, p.Prime → (p : ℝ) ≤ U i)
    (hdisj : ∀ ⦃i⦄, i ∈ input.toFinset → ∀ ⦃j⦄, j ∈ input.toFinset →
      i ≠ j → Disjoint (B i) (B j))
    (hprefix : PrefixSquareBound U Q input) :
    WellFactorable (boxProduct input.toFinset B input.count) Q := by
  have hfactors := fun Q₁ Q₂ hQ₁ hQ₂ hsplit =>
    list_boxProduct_factors input B U hU hB hdisj hprefix
      (Q₁ := Q₁) (Q₂ := Q₂) hQ₁ hQ₂ hsplit
  refine ⟨hQ, boxProduct_boundedOne _ _ _ hdisj, ?_, hfactors⟩
  obtain ⟨f, g, _, hf, _, hg, heq⟩ := hfactors Q 1 hQ le_rfl (mul_one Q)
  rw [heq]
  simpa only [mul_one] using supportedAt_mul hf hg (le_trans zero_le_one hQ)

end MathlibNt.SieveTheory.LiLiuPrereqWF
