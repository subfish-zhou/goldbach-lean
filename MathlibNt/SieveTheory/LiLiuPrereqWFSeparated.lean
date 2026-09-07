import MathlibNt.SieveTheory.LiLiuPrereqWFCommon

/-!
# Convolution across disjoint prime boxes

Disjoint prime ranges, unlike arbitrary bounded coefficients, give a unique
nonzero factorization at each integer. This controls convolutions of normalized
boxes and also allows an already constructed small-prime weight as a factor.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset

def PrimeSupported (B : Finset ℕ) (f : ArithmeticFunction ℝ) : Prop :=
  ∀ n, f n ≠ 0 → n.primeFactors ⊆ B

theorem primeSupported_mono {B C : Finset ℕ} {f : ArithmeticFunction ℝ}
    (hf : PrimeSupported B f) (hBC : B ⊆ C) : PrimeSupported C f :=
  fun n hn => (hf n hn).trans hBC

theorem primeSupported_smul {B : Finset ℕ} {f : ArithmeticFunction ℝ}
    (hf : PrimeSupported B f) (r : ℝ) : PrimeSupported B (r • f) := by
  intro n hn
  apply hf n
  intro hz
  exact hn (by simp [hz])

theorem primeSupported_one (B : Finset ℕ) :
    PrimeSupported B (1 : ArithmeticFunction ℝ) := by
  intro n hn
  by_cases h : n = 1
  · simp [h]
  · simp [h] at hn

private theorem argument_ne_zero {f : ArithmeticFunction ℝ} {n : ℕ} (hn : f n ≠ 0) :
    n ≠ 0 := by
  rintro rfl
  exact hn (by simp)

theorem primeSupported_mul {B C : Finset ℕ} {f g : ArithmeticFunction ℝ}
    (hf : PrimeSupported B f) (hg : PrimeSupported C g) :
    PrimeSupported (B ∪ C) (f * g) := by
  intro n hn
  rw [mul_apply] at hn
  obtain ⟨d, hd, hfg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨hfd, hgd⟩ := mul_ne_zero_iff.mp hfg
  have heq := (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [← heq, Nat.primeFactors_mul (argument_ne_zero hfd) (argument_ne_zero hgd)]
  exact Finset.union_subset_union (hf _ hfd) (hg _ hgd)

theorem coprime_of_separated_primes {B C : Finset ℕ} (hBC : Disjoint B C)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmB : m.primeFactors ⊆ B) (hnC : n.primeFactors ⊆ C) : m.Coprime n := by
  apply (Nat.disjoint_primeFactors hm hn).mp
  exact hBC.mono hmB hnC

/-- Two nonzero decompositions into the same disjoint prime ranges agree,
even when prime powers occur in either factor. -/
theorem separated_factorization_unique {B C : Finset ℕ} (hBC : Disjoint B C)
    {f g : ArithmeticFunction ℝ} (hf : PrimeSupported B f) (hg : PrimeSupported C g)
    {d e : ℕ × ℕ} (hd : f d.1 * g d.2 ≠ 0) (he : f e.1 * g e.2 ≠ 0)
    (hprod : d.1 * d.2 = e.1 * e.2) : d = e := by
  obtain ⟨hfd, hgd⟩ := mul_ne_zero_iff.mp hd
  obtain ⟨hfe, hge⟩ := mul_ne_zero_iff.mp he
  have hde := coprime_of_separated_primes hBC
    (argument_ne_zero hfd) (argument_ne_zero hge) (hf _ hfd) (hg _ hge)
  have hed := coprime_of_separated_primes hBC
    (argument_ne_zero hfe) (argument_ne_zero hgd) (hf _ hfe) (hg _ hgd)
  have hfirst : d.1 = e.1 := by
    apply Nat.dvd_antisymm
    · apply hde.dvd_of_dvd_mul_right
      rw [← hprod]
      exact dvd_mul_right _ _
    · apply hed.dvd_of_dvd_mul_right
      rw [hprod]
      exact dvd_mul_right _ _
  apply Prod.ext hfirst
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (argument_ne_zero hfd))
  simpa only [hfirst] using hprod

theorem boundedOne_mul_of_disjoint {B C : Finset ℕ} (hBC : Disjoint B C)
    {f g : ArithmeticFunction ℝ} (hf : PrimeSupported B f) (hg : PrimeSupported C g)
    (hfb : BoundedOne f) (hgb : BoundedOne g) : BoundedOne (f * g) := by
  intro n
  by_cases hz : (f * g) n = 0
  · simp [hz]
  have hsum : (∑ d ∈ n.divisorsAntidiagonal, f d.1 * g d.2) ≠ 0 := hz
  obtain ⟨d, hd, hfd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  rw [mul_apply, Finset.sum_eq_single_of_mem d hd, abs_mul]
  · exact mul_le_one₀ (hfb _) (abs_nonneg _) (hgb _)
  · intro e he hed
    by_contra hfe
    apply hed
    apply separated_factorization_unique hBC hf hg hfe hfd
    exact (Nat.mem_divisorsAntidiagonal.mp he).1.trans
      (Nat.mem_divisorsAntidiagonal.mp hd).1.symm

theorem primeBox_primeSupported (B : Finset ℕ) :
    PrimeSupported B (primeBox B : ArithmeticFunction ℝ) := by
  intro n hn
  by_cases h : n ∈ B ∧ n.Prime
  · rw [h.2.primeFactors]
    exact Finset.singleton_subset_iff.mpr h.1
  · simp [primeBox_apply, h] at hn

theorem primeSupported_pow {B : Finset ℕ} {f : ArithmeticFunction ℝ}
    (hf : PrimeSupported B f) (k : ℕ) : PrimeSupported B (f ^ k) := by
  induction k with
  | zero => simpa using primeSupported_one B
  | succ k ih =>
      simpa only [pow_succ, Finset.union_self] using primeSupported_mul ih hf

theorem boxWeight_primeSupported (B : Finset ℕ) (k : ℕ) :
    PrimeSupported B (boxWeight B k) :=
  primeSupported_smul (primeSupported_pow (primeBox_primeSupported B) k) _

theorem primeSupported_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : ι → Finset ℕ) (f : ι → ArithmeticFunction ℝ)
    (hf : ∀ i ∈ s, PrimeSupported (B i) (f i)) :
    PrimeSupported (s.biUnion B) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using primeSupported_one ∅
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.biUnion_insert]
      apply primeSupported_mul (hf i (Finset.mem_insert_self i s))
      exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem boundedOne_prod_of_pairwise_disjoint {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (f : ι → ArithmeticFunction ℝ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    (hf : ∀ i ∈ s, PrimeSupported (B i) (f i))
    (hb : ∀ i ∈ s, BoundedOne (f i)) : BoundedOne (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
      intro n
      by_cases hn : n = 1 <;> simp [hn]
  | @insert i s hi ih =>
      have hpair : ∀ ⦃j⦄, j ∈ s → ∀ ⦃l⦄, l ∈ s → j ≠ l → Disjoint (B j) (B l) :=
        fun _ hj _ hl hjl =>
          hdisj (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hl) hjl
      have his : Disjoint (B i) (s.biUnion B) := by
        simp only [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj)
          (by intro heq; exact hi (heq ▸ hj))
      rw [Finset.prod_insert hi]
      apply boundedOne_mul_of_disjoint his
        (hf i (Finset.mem_insert_self i s))
        (primeSupported_prod s B f (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
        (hb i (Finset.mem_insert_self i s))
      exact ih hpair (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hb j (Finset.mem_insert_of_mem hj))

/-- The normalized multi-box weight, fixed independently of all slot splits. -/
noncomputable def boxProduct {ι : Type*} (s : Finset ι)
    (B : ι → Finset ℕ) (k : ι → ℕ) : ArithmeticFunction ℝ :=
  ∏ i ∈ s, boxWeight (B i) (k i)

noncomputable def boxLeftProduct {ι : Type*} (s : Finset ι)
    (B : ι → Finset ℕ) (a b : ι → ℕ) : ArithmeticFunction ℝ :=
  ∏ i ∈ s, (((a i).factorial : ℝ) * (b i).factorial / (a i + b i).factorial) •
    boxWeight (B i) (a i)

theorem boxProduct_primeSupported {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : ι → Finset ℕ) (k : ι → ℕ) :
    PrimeSupported (s.biUnion B) (boxProduct s B k) :=
  primeSupported_prod s B _ (fun i _ => boxWeight_primeSupported (B i) (k i))

theorem boxProduct_boundedOne {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : ι → Finset ℕ) (k : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j)) :
    BoundedOne (boxProduct s B k) :=
  boundedOne_prod_of_pairwise_disjoint s B _ hdisj
    (fun i _ => boxWeight_primeSupported (B i) (k i))
    (fun i _ => boxWeight_abs_le_one (B i) (k i))

theorem boxLeftProduct_primeSupported {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : ι → Finset ℕ) (a b : ι → ℕ) :
    PrimeSupported (s.biUnion B) (boxLeftProduct s B a b) :=
  primeSupported_prod s B _
    (fun i _ => primeSupported_smul (boxWeight_primeSupported (B i) (a i)) _)

theorem boxLeftProduct_boundedOne {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : ι → Finset ℕ) (a b : ι → ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j)) :
    BoundedOne (boxLeftProduct s B a b) :=
  boundedOne_prod_of_pairwise_disjoint s B _ hdisj
    (fun i _ => primeSupported_smul (boxWeight_primeSupported (B i) (a i)) _)
    (fun i _ => (boxWeight_bounded_split (B i) (a i) (b i)).2.1)

/-- Exact multi-box convolution, without any squarefree restriction. -/
theorem boxProduct_split {ι : Type*} (s : Finset ι) (B : ι → Finset ℕ)
    (k a b : ι → ℕ) (hab : ∀ i ∈ s, a i + b i = k i) :
    boxProduct s B k = boxLeftProduct s B a b * boxProduct s B b := by
  unfold boxProduct boxLeftProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← hab i hi]
  exact (boxWeight_bounded_split (B i) (a i) (b i)).1

/-- The small-prime factor is supplied as an actual function with bounded
coefficients and separated prime support, not as a sieve conclusion record. -/
theorem smallWeight_boxProduct_bounded_split {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k a b : ι → ℕ)
    (hab : ∀ i ∈ s, a i + b i = k i)
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (B i) (B j))
    (B₀ : Finset ℕ) (ψ : ArithmeticFunction ℝ)
    (hsep : Disjoint B₀ (s.biUnion B)) (hψ : PrimeSupported B₀ ψ)
    (hψb : BoundedOne ψ) :
    ψ * boxProduct s B k = (ψ * boxLeftProduct s B a b) * boxProduct s B b ∧
      BoundedOne (ψ * boxLeftProduct s B a b) ∧ BoundedOne (boxProduct s B b) := by
  refine ⟨?_, ?_, boxProduct_boundedOne s B b hdisj⟩
  · rw [boxProduct_split s B k a b hab, mul_assoc]
  · exact boundedOne_mul_of_disjoint hsep hψ
      (boxLeftProduct_primeSupported s B a b) hψb
      (boxLeftProduct_boundedOne s B a b hdisj)

theorem prod_smul_convolution {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → ℝ) (f : ι → ArithmeticFunction ℝ) :
    (∏ i ∈ s, r i) • (∏ i ∈ s, f i) = ∏ i ∈ s, r i • f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      rw [← smul_convolution, ih]

/-- Factorial copies recover the original product of labelled-slot powers. -/
theorem factorial_mul_boxProduct {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ) :
    ((∏ i ∈ s, (k i).factorial : ℕ) : ℝ) • boxProduct s B k =
      ∏ i ∈ s, (primeBox (B i) : ArithmeticFunction ℝ) ^ k i := by
  rw [Nat.cast_prod, boxProduct, prod_smul_convolution]
  apply Finset.prod_congr rfl
  intro i _
  exact factorial_mul_dividedPower _ _

theorem sum_copies_boxProduct {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset ℕ) (k : ι → ℕ) (n : ℕ) :
    (∑ _j ∈ Finset.range (∏ i ∈ s, (k i).factorial), boxProduct s B k n) =
      (∏ i ∈ s, (primeBox (B i) : ArithmeticFunction ℝ) ^ k i) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (factorial_mul_boxProduct s B k)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_map, smul_eq_mul] using h

end MathlibNt.SieveTheory.LiLiuPrereqWF
