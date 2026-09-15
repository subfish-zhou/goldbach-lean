import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly

namespace WuPaper.R2Mother

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def upsilon1 (N : ℕ) (z : ℝ) : ℤ :=
  sieveCount N 1 N z

noncomputable def upsilon2 (N : ℕ) (w : ℝ) : ℤ :=
  sieveCount N 1 N w

noncomputable def upsilon3 (N : ℕ) (z v : ℝ) : ℤ :=
  ∑ p ∈ primeWindow N z v, sieveCount N p N z

noncomputable def upsilon4 (N : ℕ) (z u : ℝ) : ℤ :=
  ∑ p ∈ primeWindow N z u, sieveCount N p N z

noncomputable def upsilon5 (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ c ∈ primeWindow N z w, ∑ b ∈ primeWindow N z (c : ℝ),
    sieveCount N (b * c) N z

noncomputable def upsilon6 (N : ℕ) (z w u : ℝ) : ℤ :=
  ∑ c ∈ primeWindow N w u, ∑ b ∈ primeWindow N z w,
    sieveCount N (b * c) N z

noncomputable def upsilon7 (N : ℕ) (w u : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N w u).filter (fun t => u ≤ (t.1 : ℝ)),
    sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)

noncomputable def upsilon8 (N : ℕ) (z v : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z v).filter (fun t => (t.1 : ℝ) < v),
    sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)

noncomputable def upsilon9 (N : ℕ) (w u : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
    sieveCount N (t.1 * t.2) (N * t.1)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))

noncomputable def fourQuotientTerm (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  sieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)

noncomputable def upsilon10 (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
    fourQuotientTerm N t

noncomputable def upsilon11 (N : ℕ) (z w V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Range N z w V, fourQuotientTerm N t

noncomputable def eleven (N : ℕ) (z w u v V : ℝ) : ℤ :=
  3 * upsilon1 N z + upsilon2 N w - upsilon3 N z v - upsilon4 N z u +
    upsilon5 N z w + upsilon6 N z w u - 2 * upsilon7 N w u -
    upsilon8 N z v - upsilon9 N w u - upsilon10 N z w - upsilon11 N z w V

noncomputable def positiveS4 (N : ℕ) (z v : ℝ) : ℤ :=
  ∑ t ∈ orderedTriples (primeWindow N z v), s3PositiveTripleTerm N t

noncomputable def firstTriple (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ orderedTriples (primeWindow N z w),
    sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ)

noncomputable def secondTriple (N : ℕ) (z w u : ℝ) : ℤ :=
  ∑ t ∈ s3SecondRange N z w u,
    sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ)

noncomputable def delta1 (N : ℕ) (z w u : ℝ) : ℤ :=
  firstTriple N z w + secondTriple N z w u + variableS3Triples N w u

noncomputable def delta2 (N : ℕ) (z w u v : ℝ) : ℤ :=
  positiveS4 N z v - delta1 N z w u

noncomputable def firstNine (N : ℕ) (z w u v : ℝ) : ℤ :=
  3 * upsilon1 N z + upsilon2 N w - upsilon3 N z v - upsilon4 N z u +
    upsilon5 N z w + upsilon6 N z w u - 2 * upsilon7 N w u -
    upsilon8 N z v - upsilon9 N w u

theorem eleven_eq_expression (N : ℕ) (z w u v V : ℝ) :
    eleven N z w u v V =
      finiteElevenExpression N z w u v V (sieveCount N)
        (fun d y => sieveCount N d N y) := rfl

theorem eleven_eq_firstNine (N : ℕ) (z w u v V : ℝ) :
    eleven N z w u v V =
      firstNine N z w u v - upsilon10 N z w - upsilon11 N z w V := rfl

theorem delta2_eq_existing (N : ℕ) (z w u v : ℝ) :
    delta2 N z w u v = s3Delta2Quotient N z w u v := by
  unfold delta2 delta1 positiveS4 firstTriple secondTriple
    s3PositiveTripleTerm s3Delta2Quotient
  ring

theorem positiveS4_nonneg (N : ℕ) (z v : ℝ) :
    0 ≤ positiveS4 N z v :=
  sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _)

theorem upsilon2_threefold (N : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    upsilon2 N w = upsilon1 N z -
      (∑ p ∈ primeWindow N z w, sieveCount N p N z) +
      upsilon5 N z w - firstTriple N z w := by
  have h := goldbach_buchstab_threefold N 1 N hzw
  have ht := sum_s3_orderedTriples_descending N z w
    (fun t => sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ))
  simp only [one_mul] at h
  unfold upsilon2 upsilon1 upsilon5 firstTriple
  simp only [mul_comm, mul_left_comm] at h ht ⊢
  omega

theorem s1_twice (N : ℕ) {z w : ℝ} (u : ℝ) (hzw : z ≤ w) :
    (∑ p ∈ primeWindow N w u, sieveCount N p N w) =
      (∑ p ∈ primeWindow N w u, sieveCount N p N z) -
        upsilon6 N z w u + secondTriple N z w u := by
  have h := goldbach_buchstab_large_prime_sum (u := u) N 1 N hzw
  have ht := sum_s3SecondRange_descending N z w u
    (fun t => sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ))
  simp only [one_mul] at h
  unfold upsilon6 secondTriple
  simp only [mul_comm, mul_left_comm] at h ht ⊢
  omega

end WuPaper.R2Mother

#check @WuPaper.R2Mother.upsilon1
#check @WuPaper.R2Mother.upsilon2
#check @WuPaper.R2Mother.upsilon3
#check @WuPaper.R2Mother.upsilon4
#check @WuPaper.R2Mother.upsilon5
#check @WuPaper.R2Mother.upsilon6
#check @WuPaper.R2Mother.upsilon7
#check @WuPaper.R2Mother.upsilon8
#check @WuPaper.R2Mother.upsilon9
#check @WuPaper.R2Mother.fourQuotientTerm
#check @WuPaper.R2Mother.upsilon10
#check @WuPaper.R2Mother.upsilon11
#check @WuPaper.R2Mother.eleven
#check @WuPaper.R2Mother.positiveS4
#check @WuPaper.R2Mother.firstTriple
#check @WuPaper.R2Mother.secondTriple
#check @WuPaper.R2Mother.delta1
#check @WuPaper.R2Mother.delta2
#check @WuPaper.R2Mother.firstNine
#check @WuPaper.R2Mother.eleven_eq_expression
#check @WuPaper.R2Mother.eleven_eq_firstNine
#check @WuPaper.R2Mother.delta2_eq_existing
#check @WuPaper.R2Mother.positiveS4_nonneg
#check @WuPaper.R2Mother.upsilon2_threefold
#check @WuPaper.R2Mother.s1_twice
#print axioms WuPaper.R2Mother.upsilon1
#print axioms WuPaper.R2Mother.upsilon2
#print axioms WuPaper.R2Mother.upsilon3
#print axioms WuPaper.R2Mother.upsilon4
#print axioms WuPaper.R2Mother.upsilon5
#print axioms WuPaper.R2Mother.upsilon6
#print axioms WuPaper.R2Mother.upsilon7
#print axioms WuPaper.R2Mother.upsilon8
#print axioms WuPaper.R2Mother.upsilon9
#print axioms WuPaper.R2Mother.fourQuotientTerm
#print axioms WuPaper.R2Mother.upsilon10
#print axioms WuPaper.R2Mother.upsilon11
#print axioms WuPaper.R2Mother.eleven
#print axioms WuPaper.R2Mother.positiveS4
#print axioms WuPaper.R2Mother.firstTriple
#print axioms WuPaper.R2Mother.secondTriple
#print axioms WuPaper.R2Mother.delta1
#print axioms WuPaper.R2Mother.delta2
#print axioms WuPaper.R2Mother.firstNine
#print axioms WuPaper.R2Mother.eleven_eq_expression
#print axioms WuPaper.R2Mother.eleven_eq_firstNine
#print axioms WuPaper.R2Mother.delta2_eq_existing
#print axioms WuPaper.R2Mother.positiveS4_nonneg
#print axioms WuPaper.R2Mother.upsilon2_threefold
#print axioms WuPaper.R2Mother.s1_twice
