import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility
import MathlibNt.SieveTheory.LiLiuPrereqWFBoxFamily

/-!
# Real endpoint dilation and the small-weight support budget

Iwaniec's lower endpoints are dilated by `b ↦ b^(1+θ)`. Raising the
prefix-square inequalities to this power gives a budget `D^(1+θ)` for
the actual prime upper endpoints. A fixed small-prime weight at level
`D^ε` can then be placed in the larger factor for every split of the
single, fixed external level `D^(1+ε+θ)`.

The small weight is an actual supplied arithmetic function, not a sieve
conclusion record. This module does not construct the Rosser small weight
or assert its sieve direction or density.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset LiLiuPrereqWFBoxAllocation
open LiLiuPrereqWFAdmissibility

theorem prefixSquareBound_rpow {ι : Type*} (input : List ι) (b : ι → ℝ)
    {D t : ℝ} (hb : ∀ i ∈ input, 0 ≤ b i) (ht : 0 ≤ t)
    (hprefix : PrefixSquareBound b D input) :
    PrefixSquareBound (fun i => b i ^ t) (D ^ t) input := by
  intro i hi
  have hbi := hb _ (List.getElem_mem hi)
  have hp : 0 ≤ ((input.take i).map b).prod := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hb j (List.mem_of_mem_take hj)
  have hpow : (b input[i] ^ t) ^ 2 = (b input[i] ^ 2) ^ t := by
    rw [← Real.rpow_natCast (b input[i] ^ t) 2, ← Real.rpow_mul hbi,
      mul_comm t, Real.rpow_natCast_mul hbi]
  change ((input.take i).map (fun j => b j ^ t)).prod *
    (b input[i] ^ t) ^ 2 ≤ D ^ t
  rw [Real.list_prod_map_rpow' _ b (fun j hj => hb j (List.mem_of_mem_take hj)), hpow,
    ← Real.mul_rpow hp (sq_nonneg _)]
  exact Real.rpow_le_rpow (mul_nonneg hp (sq_nonneg _)) (hprefix i hi) ht

/-- Both source parities give the support budget after actual endpoint dilation. -/
theorem admissible_dilated_prefix {ι : Type*} {upper : Bool} {input : List ι}
    {b : ι → ℝ} {D θ : ℝ} (h : Admissible upper b D input) (hθ : 0 ≤ θ) :
    PrefixSquareBound (fun i => b i ^ (1 + θ)) (D ^ (1 + θ)) input :=
  prefixSquareBound_rpow input b (fun i hi => (h.one_le i hi).trans' zero_le_one)
    (by linarith) h.prefixSquareBound

/-- Occurrence allocation with the entire fixed small-prime function on the
left. The two support levels are `S*M` and `N`, with no discarded terms. -/
theorem list_smallWeight_boxProduct_factors {ι : Type*} [DecidableEq ι]
    (input : List ι) (B : ι → Finset ℕ) (U : ι → ℝ)
    (B₀ : Finset ℕ) (ψ : ArithmeticFunction ℝ) {S M N : ℝ}
    (hS : 0 ≤ S) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hU : ∀ i ∈ input.toFinset, 0 ≤ U i)
    (hB : ∀ i ∈ input.toFinset, ∀ p ∈ B i, p.Prime → (p : ℝ) ≤ U i)
    (hdisj : ∀ ⦃i⦄, i ∈ input.toFinset → ∀ ⦃j⦄, j ∈ input.toFinset →
      i ≠ j → Disjoint (B i) (B j))
    (hsep : Disjoint B₀ (input.toFinset.biUnion B))
    (hψ : PrimeSupported B₀ ψ) (hψb : BoundedOne ψ) (hψs : SupportedAt ψ S)
    (hprefix : PrefixSquareBound U (M * N) input) :
    ∃ f g : ArithmeticFunction ℝ,
      BoundedOne f ∧ SupportedAt f (S * M) ∧ BoundedOne g ∧ SupportedAt g N ∧
      ψ * boxProduct input.toFinset B input.count = f * g := by
  obtain ⟨left, right, hpart, hleft, hright⟩ :=
    exists_boxPartition_of_prefixSquareBound U hM hN input hprefix
  have hleftsub : left.toFinset ⊆ input.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hpart.sublists.1.subset (List.mem_toFinset.mp hi))
  have hrightsub : right.toFinset ⊆ input.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hpart.sublists.2.subset (List.mem_toFinset.mp hi))
  have hcounts : ∀ i ∈ input.toFinset, left.count i + right.count i = input.count i := by
    intro i _
    simpa only [List.count_append] using hpart.perm.count_eq i
  obtain ⟨heq, hfb, hgb⟩ := smallWeight_boxProduct_bounded_split
    input.toFinset B input.count left.count right.count hcounts hdisj B₀ ψ hsep hψ hψb
  refine ⟨_, _, hfb, ?_, hgb, ?_, heq⟩
  · apply supportedAt_mul hψs _ hS
    apply supportedAt_mono (boxLeftProduct_supportedAt _ _ _ _ U hU hB)
    rw [prod_pow_list_count_of_subset _ left U hleftsub]
    exact hleft
  · apply supportedAt_mono (boxProduct_supportedAt _ _ _ U hU hB)
    rw [prod_pow_list_count_of_subset _ right U hrightsub]
    exact hright

/-- If `S ≤ T`, the larger factor of `S*T` always has room for level `S`. -/
theorem small_level_le_large_factor {S T A B : ℝ}
    (hS : 1 ≤ S) (hST : S ≤ T) (hA : 1 ≤ A) (hBA : B ≤ A)
    (hsplit : A * B = S * T) : S ≤ A := by
  by_contra h
  have hAS : A < S := lt_of_not_ge h
  have hAA : A * B ≤ A * A :=
    mul_le_mul_of_nonneg_left hBA (le_trans zero_le_one hA)
  have hSS : S * S ≤ S * T :=
    mul_le_mul_of_nonneg_left hST (le_trans zero_le_one hS)
  nlinarith

/-- A supplied bounded, separated small-prime function is incorporated before
all splits. The hypothesis is a numerical endpoint budget, not WF of a weight. -/
theorem list_smallWeight_boxProduct_wellFactorable {ι : Type*} [DecidableEq ι]
    (input : List ι) (B : ι → Finset ℕ) (U : ι → ℝ)
    (B₀ : Finset ℕ) (ψ : ArithmeticFunction ℝ) {S T : ℝ}
    (hS : 1 ≤ S) (hST : S ≤ T)
    (hU : ∀ i ∈ input.toFinset, 0 ≤ U i)
    (hB : ∀ i ∈ input.toFinset, ∀ p ∈ B i, p.Prime → (p : ℝ) ≤ U i)
    (hdisj : ∀ ⦃i⦄, i ∈ input.toFinset → ∀ ⦃j⦄, j ∈ input.toFinset →
      i ≠ j → Disjoint (B i) (B j))
    (hsep : Disjoint B₀ (input.toFinset.biUnion B))
    (hψ : PrimeSupported B₀ ψ) (hψb : BoundedOne ψ) (hψs : SupportedAt ψ S)
    (hprefix : PrefixSquareBound U T input) :
    WellFactorable (ψ * boxProduct input.toFinset B input.count) (S * T) := by
  have hS₀ : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hQ : 1 ≤ S * T := by
    simpa using mul_le_mul hS (hS.trans hST) zero_le_one hS₀.le
  have hordered : ∀ A C : ℝ, 1 ≤ A → 1 ≤ C → C ≤ A → A * C = S * T →
      ∃ f g : ArithmeticFunction ℝ,
        BoundedOne f ∧ SupportedAt f A ∧ BoundedOne g ∧ SupportedAt g C ∧
        ψ * boxProduct input.toFinset B input.count = f * g := by
    intro A C hA hC hCA hsplit
    have hSA := small_level_le_large_factor hS hST hA hCA hsplit
    have hM : 1 ≤ A / S := (le_div_iff₀ hS₀).mpr (by simpa using hSA)
    have hMN : A / S * C = T := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff hS₀.ne').mpr
      simpa only [mul_comm S T] using hsplit
    have hp : PrefixSquareBound U (A / S * C) input := by
      simpa only [hMN] using hprefix
    obtain ⟨f, g, hf, hfs, hg, hgs, heq⟩ := list_smallWeight_boxProduct_factors
      input B U B₀ ψ hS₀.le hM hC hU hB hdisj hsep hψ hψb hψs hp
    have hcancel : S * (A / S) = A := by field_simp
    exact ⟨f, g, hf, by simpa only [hcancel] using hfs, hg, hgs, heq⟩
  have hall : ∀ A C : ℝ, 1 ≤ A → 1 ≤ C → A * C = S * T →
      ∃ f g : ArithmeticFunction ℝ,
        BoundedOne f ∧ SupportedAt f A ∧ BoundedOne g ∧ SupportedAt g C ∧
        ψ * boxProduct input.toFinset B input.count = f * g := by
    intro A C hA hC hsplit
    rcases le_total C A with hCA | hAC
    · exact hordered A C hA hC hCA hsplit
    · obtain ⟨f, g, hf, hfs, hg, hgs, heq⟩ :=
        hordered C A hC hA hAC (by simpa only [mul_comm] using hsplit)
      exact ⟨g, f, hg, hgs, hf, hfs, heq.trans (mul_comm f g)⟩
  refine ⟨hQ, boundedOne_mul_of_disjoint hsep hψ
    (boxProduct_primeSupported _ _ _) hψb (boxProduct_boundedOne _ _ _ hdisj), ?_, hall⟩
  obtain ⟨f, g, _, hf, _, hg, heq⟩ := hall (S * T) 1 hQ le_rfl (mul_one _)
  rw [heq]
  simpa only [mul_one] using supportedAt_mul hf hg (le_trans zero_le_one hQ)

/-- The fixed internal level `D`, the side, boxes and small weight all precede
the quantifier over external splits in `WellFactorable`. This is the real
support bridge in I80 p.312, without any split-dependent internal parameter. -/
theorem admissible_smallWeight_wellFactorable {ι : Type*} [DecidableEq ι]
    {upper : Bool} (input : List ι) (B : ι → Finset ℕ) (b : ι → ℝ)
    (B₀ : Finset ℕ) (ψ : ArithmeticFunction ℝ) {D ε θ : ℝ}
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hθ : 0 ≤ θ) (hεθ : ε ≤ 1 + θ)
    (hadm : Admissible upper b D input)
    (hB : ∀ i ∈ input.toFinset, ∀ p ∈ B i, p.Prime → (p : ℝ) ≤ b i ^ (1 + θ))
    (hdisj : ∀ ⦃i⦄, i ∈ input.toFinset → ∀ ⦃j⦄, j ∈ input.toFinset →
      i ≠ j → Disjoint (B i) (B j))
    (hsep : Disjoint B₀ (input.toFinset.biUnion B))
    (hψ : PrimeSupported B₀ ψ) (hψb : BoundedOne ψ)
    (hψs : SupportedAt ψ (D ^ ε)) :
    WellFactorable (ψ * boxProduct input.toFinset B input.count) (D ^ (1 + ε + θ)) := by
  have hD₀ : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have heq : D ^ (1 + ε + θ) = D ^ ε * D ^ (1 + θ) := by
    rw [← Real.rpow_add hD₀]
    congr 1
    ring
  rw [heq]
  exact list_smallWeight_boxProduct_wellFactorable input B (fun i => b i ^ (1 + θ)) B₀ ψ
    (Real.one_le_rpow hD hε) (Real.rpow_le_rpow_of_exponent_le hD hεθ)
    (fun i hi => Real.rpow_nonneg (le_trans zero_le_one
      (hadm.one_le i (List.mem_toFinset.mp hi))) _) hB hdisj hsep hψ hψb hψs
    (admissible_dilated_prefix hadm hθ)

end MathlibNt.SieveTheory.LiLiuPrereqWF
