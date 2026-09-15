import MathlibNt.SieveTheory.LiLiuPrereqWFBoxSquarefree
import MathlibNt.SieveTheory.LiLiuPrereqWFSeparated

/-!
# Squarefree coefficients of the existing normalized box product

Each box multiplicity contributes one coefficient, not factorially many copies.
The identities below concern the already defined full-integer arithmetic
functions. No squarefree mask or density-transfer hypothesis is introduced.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset

/-- Separated prime support determines the convolution factorization even when
one of its coefficients vanishes. No squarefreeness is needed here. -/
theorem mul_apply_of_primeSupported {B C : Finset ℕ} (hBC : Disjoint B C)
    {f g : ArithmeticFunction ℝ} (hf : PrimeSupported B f) (hg : PrimeSupported C g)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmB : m.primeFactors ⊆ B) (hnC : n.primeFactors ⊆ C) :
    (f * g) (m * n) = f m * g n := by
  rw [mul_apply]
  apply Finset.sum_eq_single_of_mem (m, n)
    (Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, mul_ne_zero hm hn⟩)
  intro d hd hne
  by_contra hterm
  obtain ⟨hfd, hgd⟩ := mul_ne_zero_iff.mp hterm
  have hd0 : d.1 ≠ 0 := by
    rintro h
    exact hfd (by simp [h])
  have hd1 : d.2 ≠ 0 := by
    rintro h
    exact hgd (by simp [h])
  have heq := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have hdn := coprime_of_separated_primes hBC hd0 hn (hf _ hfd) hnC
  have hmd := coprime_of_separated_primes hBC hm hd1 hmB (hg _ hgd)
  have hfirst : d.1 = m := by
    apply Nat.dvd_antisymm
    · apply hdn.dvd_of_dvd_mul_right
      rw [← heq]
      exact dvd_mul_right _ _
    · apply hmd.dvd_of_dvd_mul_right
      rw [heq]
      exact dvd_mul_right _ _
  apply hne
  apply Prod.ext hfirst
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm)
  simpa only [hfirst] using heq

theorem boxWeight_squarefree_eq_indicator (B : Finset ℕ) (k : ℕ) {n : ℕ}
    (hn : Squarefree n) :
    boxWeight B k n = if n.primeFactors ⊆ B ∧ n.primeFactors.card = k then 1 else 0 := by
  have hcard : cardFactors n = n.primeFactors.card := by
    exact (List.toFinset_card_of_nodup
      ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)).symm
  by_cases hB : n.primeFactors ⊆ B
  · by_cases hk : n.primeFactors.card = k
    · rw [if_pos ⟨hB, hk⟩]
      exact boxWeight_squarefree_eq_one B k hn hB (hcard.trans hk)
    · rw [if_neg (fun h => hk h.2), boxWeight_apply,
        primeBox_pow_eq_zero_of_cardFactors_ne B k n (by simpa [hcard] using hk)]
      simp
  · rw [if_neg (fun h => hB h.1)]
    by_contra hne
    exact hB (boxWeight_primeSupported B k n hne)

private theorem squarefree_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (P.prod id) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp => (hP p hp).squarefree)
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)

private theorem split_prime_product (P B : Finset ℕ) :
    (P ∩ B).prod id * (P \ B).prod id = P.prod id := by
  rw [← Finset.prod_union]
  · congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · exact Finset.disjoint_left.mpr
      (fun p hp hq => (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2)

private theorem boxProduct_primeProduct_of_subset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hsub : P ⊆ s.biUnion B) :
    boxProduct s B k (P.prod id) =
      if ∀ i ∈ s, (P ∩ B i).card = k i then 1 else 0 := by
  induction s using Finset.induction_on generalizing P with
  | empty =>
      have hP0 : P = ∅ := Finset.subset_empty.mp (by simpa using hsub)
      simp [boxProduct, hP0]
  | @insert i s hi ih =>
      have hpair : ∀ ⦃j⦄, j ∈ s → ∀ ⦃l⦄, l ∈ s → j ≠ l → Disjoint (B j) (B l) :=
        fun _ hj _ hl hjl =>
          hdisj (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hl) hjl
      have his : Disjoint (B i) (s.biUnion B) := by
        simp only [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj)
          (by intro heq; exact hi (heq ▸ hj))
      have hPL : ∀ p ∈ P ∩ B i, p.Prime :=
        fun p hp => hP p (Finset.mem_inter.mp hp).1
      have hPR : ∀ p ∈ P \ B i, p.Prime :=
        fun p hp => hP p (Finset.mem_sdiff.mp hp).1
      have hRsub : P \ B i ⊆ s.biUnion B := by
        intro p hp
        have hm := hsub (Finset.mem_sdiff.mp hp).1
        rw [Finset.biUnion_insert, Finset.mem_union] at hm
        exact hm.resolve_left (Finset.mem_sdiff.mp hp).2
      have hpfL : ((P ∩ B i).prod id).primeFactors = P ∩ B i :=
        Nat.primeFactors_prod hPL
      have hpfR : ((P \ B i).prod id).primeFactors = P \ B i :=
        Nat.primeFactors_prod hPR
      have hcounts : (∀ j ∈ s, ((P \ B i) ∩ B j).card = k j) ↔
          ∀ j ∈ s, (P ∩ B j).card = k j := by
        have hsets : ∀ j ∈ s, (P \ B i) ∩ B j = P ∩ B j := by
          intro j hj
          have hd := Finset.disjoint_left.mp
            (hdisj (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj)
              (by intro heq; exact hi (heq ▸ hj)))
          ext p
          simp only [Finset.mem_inter, Finset.mem_sdiff]
          constructor
          · exact fun h => ⟨h.1.1, h.2⟩
          · exact fun h => ⟨⟨h.1, fun hp => hd hp h.2⟩, h.2⟩
        exact ⟨fun h j hj => (hsets j hj) ▸ h j hj,
          fun h j hj => (hsets j hj).symm ▸ h j hj⟩
      have hprod : boxProduct (insert i s) B k = boxWeight (B i) (k i) * boxProduct s B k := by
        simp only [boxProduct, Finset.prod_insert hi]
      rw [hprod, ← split_prime_product P (B i),
        mul_apply_of_primeSupported his (boxWeight_primeSupported (B i) (k i))
          (boxProduct_primeSupported s B k)
          (squarefree_prime_product _ hPL).ne_zero (squarefree_prime_product _ hPR).ne_zero
          (by simpa only [hpfL] using (Finset.inter_subset_right : P ∩ B i ⊆ B i))
          (by simpa only [hpfR] using hRsub),
        boxWeight_squarefree_eq_indicator (B i) (k i) (squarefree_prime_product _ hPL),
        ih hpair (P \ B i) hPR hRsub]
      simp only [hpfL, Finset.inter_subset_right, true_and, hcounts,
        Finset.forall_mem_insert]
      split_ifs <;> simp_all

/-- On a finite product of distinct primes, the normalized box product is the
indicator of complete box support and the prescribed multiplicity in every box.
The boxes themselves may contain nonprimes, which the existing weight ignores. -/
theorem boxProduct_primeProduct_eq_indicator {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    boxProduct s B k (P.prod id) =
      if P ⊆ s.biUnion B ∧ (∀ i ∈ s, (P ∩ B i).card = k i) then 1 else 0 := by
  by_cases hsub : P ⊆ s.biUnion B
  · simpa only [hsub, true_and] using
      boxProduct_primeProduct_of_subset s B k hdisj P hP hsub
  · rw [if_neg (fun h => hsub h.1)]
    by_contra hne
    have hs := boxProduct_primeSupported s B k (P.prod id) hne
    exact hsub (by simpa only [id_eq, Nat.primeFactors_prod hP] using hs)

/-- The existing full-integer `boxProduct` has coefficient exactly one on the
squarefree integers with the prescribed box counts, and zero on all other
squarefree integers. -/
theorem boxProduct_squarefree_eq_indicator {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    {n : ℕ} (hn : Squarefree n) :
    boxProduct s B k n =
      if n.primeFactors ⊆ s.biUnion B ∧
        (∀ i ∈ s, (n.primeFactors ∩ B i).card = k i) then 1 else 0 := by
  simpa only [id_eq, Nat.prod_primeFactors_of_squarefree hn] using
    boxProduct_primeProduct_eq_indicator s B k hdisj n.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)

theorem boxProduct_squarefree_eq_one_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    {n : ℕ} (hn : Squarefree n) :
    boxProduct s B k n = 1 ↔ n.primeFactors ⊆ s.biUnion B ∧
      (∀ i ∈ s, (n.primeFactors ∩ B i).card = k i) := by
  rw [boxProduct_squarefree_eq_indicator s B k hdisj hn]
  split_ifs <;> simp_all

theorem boxProduct_squarefree_eq_zero_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    {n : ℕ} (hn : Squarefree n) :
    boxProduct s B k n = 0 ↔ ¬ (n.primeFactors ⊆ s.biUnion B ∧
      (∀ i ∈ s, (n.primeFactors ∩ B i).card = k i)) := by
  rw [boxProduct_squarefree_eq_indicator s B k hdisj hn]
  split_ifs <;> simp_all

/-- The actual small-prime coefficient survives the canonical small/big split.
Only its prime support is assumed; no boundedness, sign, or sieve conclusion is
required. A prescribed box multiplicity contributes once, not `∏ i, (k i)!` times. -/
theorem smallWeight_boxProduct_primeProduct_eq_indicator {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    (B₀ : Finset ℕ) (ψ : ArithmeticFunction ℝ)
    (hsep : Disjoint B₀ (s.biUnion B)) (hψ : PrimeSupported B₀ ψ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (ψ * boxProduct s B k) (P.prod id) =
      if P ⊆ B₀ ∪ s.biUnion B ∧ (∀ i ∈ s, (P ∩ B i).card = k i)
      then ψ ((P ∩ B₀).prod id) else 0 := by
  by_cases hsub : P ⊆ B₀ ∪ s.biUnion B
  · have hPL : ∀ p ∈ P ∩ B₀, p.Prime :=
      fun p hp => hP p (Finset.mem_inter.mp hp).1
    have hPR : ∀ p ∈ P \ B₀, p.Prime :=
      fun p hp => hP p (Finset.mem_sdiff.mp hp).1
    have hRsub : P \ B₀ ⊆ s.biUnion B := by
      intro p hp
      exact (Finset.mem_union.mp (hsub (Finset.mem_sdiff.mp hp).1)).resolve_left
        (Finset.mem_sdiff.mp hp).2
    have hpfL : ((P ∩ B₀).prod id).primeFactors = P ∩ B₀ :=
      Nat.primeFactors_prod hPL
    have hpfR : ((P \ B₀).prod id).primeFactors = P \ B₀ :=
      Nat.primeFactors_prod hPR
    have hcounts : (∀ i ∈ s, ((P \ B₀) ∩ B i).card = k i) ↔
        ∀ i ∈ s, (P ∩ B i).card = k i := by
      have hsets : ∀ i ∈ s, (P \ B₀) ∩ B i = P ∩ B i := by
        intro i hi
        ext p
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · exact fun h => ⟨⟨h.1, fun hp => Finset.disjoint_left.mp hsep hp
            (Finset.mem_biUnion.mpr ⟨i, hi, h.2⟩)⟩, h.2⟩
      exact ⟨fun h i hi => (hsets i hi) ▸ h i hi,
        fun h i hi => (hsets i hi).symm ▸ h i hi⟩
    rw [← split_prime_product P B₀,
      mul_apply_of_primeSupported hsep hψ (boxProduct_primeSupported s B k)
        (squarefree_prime_product _ hPL).ne_zero (squarefree_prime_product _ hPR).ne_zero
        (by simpa only [hpfL] using (Finset.inter_subset_right : P ∩ B₀ ⊆ B₀))
        (by simpa only [hpfR] using hRsub),
      boxProduct_primeProduct_eq_indicator s B k hdisj (P \ B₀) hPR]
    simp only [hsub, hRsub, true_and, hcounts]
    split_ifs <;> simp
  · rw [if_neg (fun h => hsub h.1)]
    by_contra hne
    have hs := primeSupported_mul hψ (boxProduct_primeSupported s B k) (P.prod id) hne
    exact hsub (by simpa only [id_eq, Nat.primeFactors_prod hP] using hs)

/-- Canonical small/big prime-factor splitting at every squarefree integer,
including integers outside the combined prime support (where the value is zero). -/
theorem smallWeight_boxProduct_squarefree_eq_indicator {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    (B₀ : Finset ℕ) (ψ : ArithmeticFunction ℝ)
    (hsep : Disjoint B₀ (s.biUnion B)) (hψ : PrimeSupported B₀ ψ)
    {n : ℕ} (hn : Squarefree n) :
    (ψ * boxProduct s B k) n =
      if n.primeFactors ⊆ B₀ ∪ s.biUnion B ∧
        (∀ i ∈ s, (n.primeFactors ∩ B i).card = k i)
      then ψ ((n.primeFactors ∩ B₀).prod id) else 0 := by
  simpa only [id_eq, Nat.prod_primeFactors_of_squarefree hn] using
    smallWeight_boxProduct_primeProduct_eq_indicator s B k hdisj B₀ ψ hsep hψ
      n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)

#check mul_apply_of_primeSupported
#print axioms mul_apply_of_primeSupported
#check boxWeight_squarefree_eq_indicator
#print axioms boxWeight_squarefree_eq_indicator
#check boxProduct_primeProduct_eq_indicator
#print axioms boxProduct_primeProduct_eq_indicator
#check boxProduct_squarefree_eq_indicator
#print axioms boxProduct_squarefree_eq_indicator
#check boxProduct_squarefree_eq_one_iff
#print axioms boxProduct_squarefree_eq_one_iff
#check boxProduct_squarefree_eq_zero_iff
#print axioms boxProduct_squarefree_eq_zero_iff
#check smallWeight_boxProduct_primeProduct_eq_indicator
#print axioms smallWeight_boxProduct_primeProduct_eq_indicator
#check smallWeight_boxProduct_squarefree_eq_indicator
#print axioms smallWeight_boxProduct_squarefree_eq_indicator

end MathlibNt.SieveTheory.LiLiuPrereqWF
