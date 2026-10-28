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


end MathlibNt.SieveTheory.LiLiuPrereqWF
