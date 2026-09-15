import MathlibNt.Wu2008DoubleSieve.SignedFiniteAssembly

/-!
# Both lower weights and the eleven-term expression

Wu08, Lemma 2.2, (2.3)--(2.6), source lines 293--527.  The first
lower weight's positive S4, the variable-cutoff slack, and both outer
lower-weight slacks are retained.  No comparison of B11 alone is needed
for the resulting exact identity.

`finiteElevenExpression` separates the first nine carrier evaluations
from the four-prime evaluations. This permits an exact, signed transport
from quotient / P(d*N) majorants to the literal unscaled P(N)/P(N*a)
expression, rather than an invalid replacement inside a negative term.
All cutoffs here are strict; the printed closed convention is separate.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem sum_s3_orderedTriples_descending (N : ℕ) (z w : ℝ)
    (f : ℕ × ℕ × ℕ → ℤ) :
    ∑ t ∈ orderedTriples (primeWindow N z w), f t =
      ∑ c ∈ primeWindow N z w, ∑ b ∈ primeWindow N z (c : ℝ),
        ∑ a ∈ primeWindow N z (b : ℝ), f (a, b, c) := by
  rw [sum_sigma']
  rw [sum_sigma']
  apply sum_bij (fun t _ => ⟨⟨t.2.2, t.2.1⟩, t.1⟩)
  · rintro ⟨a, b, c⟩ ht
    obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hcw, hab, hbc⟩ :=
      mem_s3_ordered_triples.mp ht
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
    exact mem_sigma.mpr ⟨mem_sigma.mpr
      ⟨mem_primeWindow.mpr ⟨hc, hcN, (hza.trans hab'.le).trans hbc'.le, hcw⟩,
        mem_primeWindow.mpr ⟨hb, hbN, hza.trans hab'.le, hbc'⟩⟩,
      mem_primeWindow.mpr ⟨ha, haN, hza, hab'⟩⟩
  · rintro ⟨a, b, c⟩ _ ⟨a', b', c'⟩ _ h
    have hc := congrArg (fun t => t.1.1) h
    have hb := congrArg (fun t => t.1.2) h
    have ha := congrArg (fun t => t.2) h
    dsimp only at hc hb ha
    subst a'; subst b'; subst c'
    rfl
  · rintro ⟨⟨c, b⟩, a⟩ ht
    obtain ⟨hcb, ha⟩ := mem_sigma.mp ht
    obtain ⟨hc, hb⟩ := mem_sigma.mp hcb
    obtain ⟨ha, haN, hza, hab⟩ := mem_primeWindow.mp ha
    obtain ⟨hb, hbN, _, hbc⟩ := mem_primeWindow.mp hb
    obtain ⟨hc, hcN, _, hcw⟩ := mem_primeWindow.mp hc
    exact ⟨(a, b, c), mem_s3_ordered_triples.mpr
      ⟨ha, haN, hza, hb, hbN, hc, hcN, hcw,
        by exact_mod_cast hab, by exact_mod_cast hbc⟩, rfl⟩
  · intro t _
    rfl

theorem sum_s3SecondRange_descending (N : ℕ) (z w u : ℝ)
    (f : ℕ × ℕ × ℕ → ℤ) :
    ∑ t ∈ s3SecondRange N z w u, f t =
      ∑ c ∈ primeWindow N w u, ∑ b ∈ primeWindow N z w,
        ∑ a ∈ primeWindow N z (b : ℝ), f (a, b, c) := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun t _ => ⟨⟨t.2.2, t.2.1⟩, t.1⟩)
  · rintro ⟨a, b, c⟩ ht
    obtain ⟨ht, hbw, hwc⟩ := mem_filter.mp ht
    obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hcu, hab, _⟩ :=
      mem_s3_ordered_triples.mp ht
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    exact mem_sigma.mpr ⟨mem_sigma.mpr
      ⟨mem_primeWindow.mpr ⟨hc, hcN, hwc, hcu⟩,
        mem_primeWindow.mpr ⟨hb, hbN, hza.trans hab'.le, hbw⟩⟩,
      mem_primeWindow.mpr ⟨ha, haN, hza, hab'⟩⟩
  · rintro ⟨a, b, c⟩ _ ⟨a', b', c'⟩ _ h
    have hc := congrArg (fun t => t.1.1) h
    have hb := congrArg (fun t => t.1.2) h
    have ha := congrArg (fun t => t.2) h
    dsimp only at hc hb ha
    subst a'; subst b'; subst c'
    rfl
  · rintro ⟨⟨c, b⟩, a⟩ ht
    obtain ⟨hcb, ha⟩ := mem_sigma.mp ht
    obtain ⟨hc, hb⟩ := mem_sigma.mp hcb
    obtain ⟨ha, haN, hza, hab⟩ := mem_primeWindow.mp ha
    obtain ⟨hb, hbN, _, hbw⟩ := mem_primeWindow.mp hb
    obtain ⟨hc, hcN, hwc, hcu⟩ := mem_primeWindow.mp hc
    refine ⟨(a, b, c), mem_filter.mpr ⟨mem_s3_ordered_triples.mpr
      ⟨ha, haN, hza, hb, hbN, hc, hcN, hcu,
        by exact_mod_cast hab, by exact_mod_cast hbw.trans_le hwc⟩, hbw, hwc⟩, rfl⟩
  · intro t _
    rfl

theorem sum_primeWindow_split (N : ℕ) {z w u : ℝ} (hzw : z ≤ w) (hwu : w ≤ u)
    (f : ℕ → ℤ) :
    (∑ p ∈ primeWindow N z u, f p) =
      (∑ p ∈ primeWindow N z w, f p) + ∑ p ∈ primeWindow N w u, f p := by
  have he : primeWindow N z u = primeWindow N z w ∪ primeWindow N w u := by
    ext p
    simp only [mem_union, mem_primeWindow]
    constructor
    · rintro ⟨hp, hcop, hz, hu⟩
      by_cases hw : (p : ℝ) < w
      · exact Or.inl ⟨hp, hcop, hz, hw⟩
      · exact Or.inr ⟨hp, hcop, le_of_not_gt hw, hu⟩
    · rintro (⟨hp, hcop, hz, hw⟩ | ⟨hp, hcop, hw, hu⟩)
      · exact ⟨hp, hcop, hz, hw.trans_le hwu⟩
      · exact ⟨hp, hcop, hzw.trans hw, hu⟩
  rw [he, sum_union]
  exact disjoint_left.mpr (fun p hp hq =>
    (not_lt_of_ge (mem_primeWindow.mp hq).2.2.1) (mem_primeWindow.mp hp).2.2.2)

/-- The two pair sums are ordered by their larger prime, with multiplicity
one. `S` handles terms 1--9, and `Q` handles terms 10--11 at P(N). -/
noncomputable def finiteElevenExpression (N : ℕ) (z w u v V : ℝ)
    (S : ℕ → ℕ → ℝ → ℤ) (Q : ℕ → ℝ → ℤ) : ℤ :=
  3 * S 1 N z + S 1 N w -
    (∑ p ∈ primeWindow N z v, S p N z) -
    (∑ p ∈ primeWindow N z u, S p N z) +
    (∑ c ∈ primeWindow N z w, ∑ b ∈ primeWindow N z (c : ℝ), S (b * c) N z) +
    (∑ c ∈ primeWindow N w u, ∑ b ∈ primeWindow N z w, S (b * c) N z) -
    2 * (∑ t ∈ (lowerPairs N N w u).filter (fun t => u ≤ (t.1 : ℝ)),
      S (t.1 * t.2) (N * t.1) (t.2 : ℝ)) -
    (∑ t ∈ (lowerPairs N N z v).filter (fun t => (t.1 : ℝ) < v),
      S (t.1 * t.2) (N * t.1) (t.2 : ℝ)) -
    (∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
      S (t.1 * t.2) (N * t.1)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))) -
    (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
      Q (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) (t.2.1 : ℝ)) -
    ∑ t ∈ s3Upsilon11Range N z w V,
      Q (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) (t.2.1 : ℝ)

noncomputable def finiteElevenMixed (N : ℕ) (z w u v V : ℝ) : ℤ :=
  finiteElevenExpression N z w u v V (sieveCount N)
    (fun d y => sourceSieveCount N d (d * N) y)

noncomputable def s3PairRepeatedBudget (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ lowerPairs N N z w,
    ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℤ)

noncomputable def s3VariableSlack (N : ℕ) (z w : ℝ) : ℤ :=
  variableS3Main N z w + variableS3Triples N z w +
    s3PairRepeatedBudget N z w - lowerS3 N z w

theorem s3VariableSlack_nonneg (N : ℕ) (z w : ℝ) :
    0 ≤ s3VariableSlack N z w :=
  sub_nonneg.mpr (lowerS3_le_variable_add_square_error N z w)

/-- The exact predecessor of (2.6). In particular, the S4 from the first
outer weight is still present, and the S3 inequality has its actual slack. -/
theorem finiteElevenMixed_exact_lower_weights (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) :
    lowerWeightRHS N w u + lowerWeightRHS N z v =
      finiteElevenMixed N z w u v V + s3Delta2Quotient N z w u v +
        s3FourSourceMajorant N (orderedTriples (primeWindow N z w)) +
        s3Upsilon11Source N z w V +
        (∑ t ∈ orderedTriples (primeWindow N w u), s3PositiveTripleTerm N t) +
        s3VariableSlack N w u - s3PairRepeatedBudget N w u -
        2 * lowerS2 N z v := by
  have hbase := goldbach_buchstab_threefold N 1 N hzw
  have hsingle := goldbach_buchstab_large_prime_sum (u := u) N 1 N hzw
  have hsplit := sum_primeWindow_split N hzw hwu (fun p => sieveCount N p N z)
  have hA := sum_s3_orderedTriples_descending N z w
    (fun t => sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ))
  have hB := sum_s3SecondRange_descending N z w u
    (fun t => sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ))
  simp only [one_mul] at hbase hsingle
  simp only [mul_comm, mul_left_comm] at hbase hsingle hA hB
  unfold lowerWeightRHS finiteElevenMixed finiteElevenExpression s3Delta2Quotient
    s3VariableSlack s3FourSourceMajorant s3Upsilon11Source s3FourSourceTerm
    s3PositiveTripleTerm lowerS2 lowerS3 variableS3Main
  change _ = _
  simp only [mul_comm, mul_left_comm] at hsplit ⊢
  omega

theorem lowerS2_eq_zero_of_cubic_cutoff {N : ℕ} {z v : ℝ}
    (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3) :
    lowerS2 N z v = 0 := by
  apply sum_eq_zero
  intro t ht
  obtain ⟨ht, hva⟩ := mem_filter.mp ht
  have hsize := (mem_filter.mp ht).2.2
  have hab := (mem_filter.mp ht).2.1
  have hvb : v ≤ (t.2 : ℝ) :=
    hva.trans (by exact_mod_cast hab.le)
  have hmul := mul_le_mul hva (pow_le_pow_left₀ hv hvb 2)
    (sq_nonneg v) (Nat.cast_nonneg t.1)
  have hsize' : (t.1 : ℝ) * (t.2 : ℝ) ^ 2 < N := by exact_mod_cast hsize
  nlinarith

noncomputable def lowerWeightOuterSlack (N : ℕ) (z w : ℝ) : ℝ :=
  2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
    (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) -
    (lowerWeightRHS N z w : ℝ)

theorem lowerWeightOuterSlack_nonneg {N : ℕ} (hN : 0 < N)
    {z : ℝ} (hz : 2 ≤ z) (w : ℝ) :
    0 ≤ lowerWeightOuterSlack N z w := by
  have h := lowerWeightRHS_le_count_add_explicit_error hN hz w
  unfold lowerWeightOuterSlack
  linarith

/-- An exact identity against the actual representation count, including
both nonnegative outer slacks. The entire unpaid quantity is signed. -/
theorem finiteElevenMixed_exact_count (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) (hwv : w ≤ v) (huv : u ≤ v)
    (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) +
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) =
      (finiteElevenMixed N z w u v V : ℝ) +
        (s3RetainedTripleMass N z w u v : ℝ) +
        (s3FourModulusGain N (orderedTriples (primeWindow N z w)) : ℝ) +
        (s3FourModulusGain N (s3SecondRange N z w u) : ℝ) +
        (s3Upsilon11MissingMass N z w u V : ℝ) -
        (s3Upsilon11ExcessMass N z w u V : ℝ) -
        (s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) : ℝ) -
        (s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) : ℝ) +
        (∑ t ∈ orderedTriples (primeWindow N w u), s3PositiveTripleTerm N t : ℤ) +
        (s3VariableSlack N w u : ℝ) - (s3PairRepeatedBudget N w u : ℝ) +
        lowerWeightOuterSlack N w u + lowerWeightOuterSlack N z v := by
  have hW := finiteElevenMixed_exact_lower_weights N z w u v V hzw hwu
  have hD := s3_delta2_exact_moving N z w u v V hwv huv hthird
  have hzero : lowerS2 N z v = 0 := lowerS2_eq_zero_of_cubic_cutoff hv hNv
  rw [hzero] at hW
  have hW' := congrArg (fun x : ℤ => (x : ℝ)) hW
  have hD' := congrArg (fun x : ℤ => (x : ℝ)) hD
  push_cast at hW' hD'
  unfold lowerWeightOuterSlack
  simp only [Int.cast_sum]
  linarith

theorem finiteElevenExpression_sub (N : ℕ) (z w u v V : ℝ)
    (S T : ℕ → ℕ → ℝ → ℤ) (Q R : ℕ → ℝ → ℤ) :
    finiteElevenExpression N z w u v V (fun d M y => S d M y - T d M y)
        (fun d y => Q d y - R d y) =
      finiteElevenExpression N z w u v V S Q -
        finiteElevenExpression N z w u v V T R := by
  simp only [finiteElevenExpression, sum_sub_distrib]
  ring

/-- Literal unscaled strict carrier specialization of all eleven terms. -/
noncomputable def finiteElevenUnscaled (N : ℕ) (z w u v V : ℝ) : ℤ :=
  finiteElevenExpression N z w u v V (sourceSieveCount N)
    (fun d y => sourceSieveCount N d N y)

/-- Signed, term-by-term carrier transport. Its negative coefficients are
not replaced by positive majorants, and no smallness is asserted. -/
theorem finiteElevenMixed_eq_unscaled_add_signed_transport
    (N : ℕ) (z w u v V : ℝ) :
    finiteElevenMixed N z w u v V =
      finiteElevenUnscaled N z w u v V +
        finiteElevenExpression N z w u v V
          (fun d M y => sieveCount N d M y - sourceSieveCount N d M y)
          (fun d y => sourceSieveCount N d (d * N) y - sourceSieveCount N d N y) := by
  rw [finiteElevenExpression_sub]
  change finiteElevenMixed N z w u v V = finiteElevenUnscaled N z w u v V +
    (finiteElevenMixed N z w u v V - finiteElevenUnscaled N z w u v V)
  omega

/-- All restored positive contributions, including both outer slacks.
This is an actual finite sum, not a premise encoding the desired payment. -/
noncomputable def finiteAssemblyGains (N : ℕ) (z w u v V : ℝ) : ℝ :=
  (s3RetainedTripleMass N z w u v : ℝ) +
    (s3FourModulusGain N (orderedTriples (primeWindow N z w)) : ℝ) +
    (s3FourModulusGain N (s3SecondRange N z w u) : ℝ) +
    (s3Upsilon11MissingMass N z w u V : ℝ) +
    (∑ t ∈ orderedTriples (primeWindow N w u), s3PositiveTripleTerm N t : ℤ) +
    (s3VariableSlack N w u : ℝ) +
    lowerWeightOuterSlack N w u + lowerWeightOuterSlack N z v

theorem finiteAssemblyGains_nonneg {N : ℕ} (hN : 0 < N)
    {z w : ℝ} (hz : 2 ≤ z) (hw : 2 ≤ w) (u v V : ℝ) :
    0 ≤ finiteAssemblyGains N z w u v V := by
  have hT : 0 ≤ (∑ t ∈ orderedTriples (primeWindow N w u),
      s3PositiveTripleTerm N t : ℤ) :=
    sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _)
  have hR := Int.cast_nonneg (R := ℝ) (s3RetainedTripleMass_nonneg N z w u v)
  have hA := Int.cast_nonneg (R := ℝ)
    (s3FourModulusGain_nonneg N (orderedTriples (primeWindow N z w)))
  have hB := Int.cast_nonneg (R := ℝ)
    (s3FourModulusGain_nonneg N (s3SecondRange N z w u))
  have hM := Int.cast_nonneg (R := ℝ) (s3Upsilon11MissingMass_nonneg N z w u V)
  have hS := Int.cast_nonneg (R := ℝ) (s3VariableSlack_nonneg N w u)
  have hT' := Int.cast_nonneg (R := ℝ) hT
  have hwS := lowerWeightOuterSlack_nonneg hN hw u
  have hzS := lowerWeightOuterSlack_nonneg hN hz v
  unfold finiteAssemblyGains
  linarith

theorem finiteElevenMixed_exact_aggregate (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) (hwv : w ≤ v) (huv : u ≤ v)
    (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) +
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) =
      (finiteElevenMixed N z w u v V : ℝ) + finiteAssemblyGains N z w u v V -
        (s3Upsilon11ExcessMass N z w u V : ℝ) -
        (s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) : ℝ) -
        (s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) : ℝ) -
        (s3PairRepeatedBudget N w u : ℝ) := by
  have h := finiteElevenMixed_exact_count N z w u v V
    hzw hwu hwv huv hv hNv hthird
  unfold finiteAssemblyGains
  linarith

/-- At the source parameters all repeated-prime contributions and both
outer error bounds are paid. What remains is the signed aggregate
`X11 - finiteAssemblyGains`, where X11 is the actual rectangular-only
mass; the historical floor-count bound B11 is only an upper bound for X11. -/
theorem finiteElevenMixed_le_count_signed_paid {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (finiteElevenMixed N z w u v V : ℝ) + finiteAssemblyGains N z w u v V -
        (s3Upsilon11ExcessMass N z w u V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzw := Real.rpow_le_rpow_of_exponent_le hN1 hκ
  have hwu := Real.rpow_le_rpow_of_exponent_le hN1
    (show κ₂ ≤ 1 / 2 - 3 * κ₁ by linarith)
  have hwv := Real.rpow_le_rpow_of_exponent_le hN1
    (show κ₂ ≤ 1 / 3 by linarith)
  have huv := Real.rpow_le_rpow_of_exponent_le hN1
    (show 1 / 2 - 3 * κ₁ ≤ 1 / 3 by linarith)
  have hv : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hN0.le _
  have hNv : (N : ℝ) ≤ ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hE := finiteElevenMixed_exact_aggregate N _ _ _ _
    ((N : ℝ) ^ (1 / 2 - 2 * κ₁)) hzw hwu hwv huv hv hNv
    (s3ThirdRange_subset_source_triples (by omega) hκ hparam)
  have hR := s3_repeated_first_two_ranges_le hN he (by linarith : 0 < κ₁) hz hwu
  have hP := pair_endpoint_sum_le hN he (by linarith : 0 < κ₂) (hz.trans hzw) hwu
  have hdiv : (N : ℝ) / (N : ℝ) ^ κ₂ = (N : ℝ) ^ (1 - κ₂) := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
  rw [hdiv] at hP
  have hP' : (s3PairRepeatedBudget N ((N : ℝ) ^ κ₂)
      ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) : ℝ) ≤
        2 * (1 / κ₂) ^ 2 * (N : ℝ) ^ (1 - κ₂) := by
    simpa only [s3PairRepeatedBudget, Int.cast_sum, Int.cast_natCast] using hP
  have hpw := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - κ₂ ≤ 1 - κ₁ by linarith)
  have hP'' := hP'.trans (mul_le_mul_of_nonneg_left hpw
    (show 0 ≤ 2 * (1 / κ₂) ^ 2 by positivity))
  have hEw := lowerWeight_error_le_rpow (by omega : 0 < N)
    (show κ₂ ≤ 1 / 2 by linarith)
  have hEz := lowerWeight_error_le_rpow (by omega : 0 < N)
    (show κ₁ ≤ 1 / 2 by linarith)
  nlinarith

/-- A source-carrier consumer with no new mathematical hypothesis on the
counts: every change of carrier is retained in the signed linear expression.
Specialize `S = sourceSieveCount N`, `Q d y = sourceSieveCount N d N y`
for strict unscaled carriers, or both to `sourceSieveCountLE` for the
literal closed unscaled convention. In neither case is the transport free. -/
theorem finiteElevenExpression_le_count_signed_paid {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁)
    (S : ℕ → ℕ → ℝ → ℤ) (Q : ℕ → ℝ → ℤ) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (finiteElevenExpression N z w u v V S Q : ℝ) +
        (finiteElevenExpression N z w u v V
          (fun d M y => sieveCount N d M y - S d M y)
          (fun d y => sourceSieveCount N d (d * N) y - Q d y) : ℝ) +
        finiteAssemblyGains N z w u v V -
        (s3Upsilon11ExcessMass N z w u V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  have h := finiteElevenMixed_le_count_signed_paid hN he hκ₁ hκ hupper hparam hz
  dsimp only at h ⊢
  rw [finiteElevenExpression_sub, Int.cast_sub]
  change _ ≤ _
  unfold finiteElevenMixed at h
  linarith

end Wu2008DoubleSieve
