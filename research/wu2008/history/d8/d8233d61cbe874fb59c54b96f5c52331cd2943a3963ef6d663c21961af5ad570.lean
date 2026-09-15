import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly

/-!
# The sign of the literal unscaled transport

The four-prime terms at `P(N)` vanish: their first selected prime is
strictly below the second-prime cutoff. This is a whole-carrier effect,
not a repeated-prime error. The transport in the accepted eleven-term
consumer is therefore negative, including the variable-cutoff crossing
correction with its negative sign.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem jointResidual_source_four_zero {N a b c d : ℕ}
    (ha : a.Prime) (haN : a.Coprime N) (hab : a < b) :
    sourceSieveCount N (a * b * c * d) N (b : ℝ) = 0 ∧
      sourceSieveCountLE N (a * b * c * d) N (b : ℝ) = 0 := by
  have hd : a ∣ a * b * c * d :=
    (dvd_mul_right a b).trans
      ((dvd_mul_right (a * b) c).trans (dvd_mul_right (a * b * c) d))
  have he := sourceSieveCarrier_eq_empty_of_selected
    (N := N) (z := (b : ℝ)) ha haN hd (by exact_mod_cast hab)
  constructor
  · simp only [sourceSieveCount, he, card_empty, Nat.cast_zero]
  · have he' : sourceSieveCarrierLE N (a * b * c * d) N (b : ℝ) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨_, _, hdp, hs⟩ := mem_filter.mp hp
      exact hs a ha haN (by exact_mod_cast hab.le) (hd.trans hdp)
    simp only [sourceSieveCountLE, he', card_empty, Nat.cast_zero]

theorem jointResidual_source_four_sums_zero (N : ℕ) (z w V : ℝ) :
    (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
      sourceSieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)) = 0 ∧
    (∑ t ∈ s3Upsilon11Range N z w V,
      sourceSieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)) = 0 := by
  constructor
  · apply sum_eq_zero
    rintro ⟨a, b, c, d⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, _, _, hab, _⟩ :=
      mem_s3_first_quadruples.mp ht
    exact (jointResidual_source_four_zero ha haN hab).1
  · apply sum_eq_zero
    rintro ⟨a, b, c, d⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, _, hab, _⟩ :=
      mem_s3Upsilon11Range.mp ht
    exact (jointResidual_source_four_zero ha haN hab).1

theorem jointResidual_strict_transport (N : ℕ) (z w u v V : ℝ) :
    finiteElevenExpression N z w u v V
        (fun d M y => sieveCount N d M y - sourceSieveCount N d M y)
        (fun d y => sourceSieveCount N d (d * N) y - sourceSieveCount N d N y) =
      -variableS3CrossingCorrection N w u -
        s3FourSourceMajorant N (orderedTriples (primeWindow N z w)) -
        s3Upsilon11Source N z w V := by
  have hbase (y : ℝ) : sieveCount N 1 N y = sourceSieveCount N 1 N y := by
    simp only [sourceSieveCount, sieveCount,
      sourceSieveCarrier_of_dvd_modulus N (one_dvd N)]
  have hsingle (y : ℝ) :
      (∑ p ∈ primeWindow N z y, (sieveCount N p N z - sourceSieveCount N p N z)) = 0 := by
    apply sum_eq_zero
    intro p hp
    obtain ⟨hp, _, hz, _⟩ := mem_primeWindow.mp hp
    simp only [sourceSieveCount, sieveCount, sourceSieveCarrier_eq_ite,
      if_pos (sifted_prime_of_le hp hz), sub_self]
  have hpair {b c : ℕ} (hb : b.Prime) (hc : c.Prime)
      (hzb : z ≤ (b : ℝ)) (hzc : z ≤ (c : ℝ)) :
      sieveCount N (b * c) N z - sourceSieveCount N (b * c) N z = 0 := by
    simp only [sourceSieveCount, sieveCount, sourceSieveCarrier_eq_ite,
      if_pos ((sifted_mul_iff N b c z).mpr
        ⟨sifted_prime_of_le hb hzb, sifted_prime_of_le hc hzc⟩), sub_self]
  have hA :
      (∑ c ∈ primeWindow N z w, ∑ b ∈ primeWindow N z (c : ℝ),
        (sieveCount N (b * c) N z - sourceSieveCount N (b * c) N z)) = 0 := by
    apply sum_eq_zero
    intro c hc
    apply sum_eq_zero
    intro b hb
    exact hpair (mem_primeWindow.mp hb).1 (mem_primeWindow.mp hc).1
      (mem_primeWindow.mp hb).2.2.1 (mem_primeWindow.mp hc).2.2.1
  have hB :
      (∑ c ∈ primeWindow N w u, ∑ b ∈ primeWindow N z w,
        (sieveCount N (b * c) N z - sourceSieveCount N (b * c) N z)) = 0 := by
    apply sum_eq_zero
    intro c hc
    apply sum_eq_zero
    intro b hb
    exact hpair (mem_primeWindow.mp hb).1 (mem_primeWindow.mp hc).1
      (mem_primeWindow.mp hb).2.2.1
      ((mem_primeWindow.mp hb).2.2.1.trans
        ((mem_primeWindow.mp hb).2.2.2.le.trans (mem_primeWindow.mp hc).2.2.1))
  have hpairs (x y : ℝ) (f : ℕ × ℕ → Prop) [DecidablePred f] :
      (∑ t ∈ (lowerPairs N N x y).filter f,
        (sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ) -
          sourceSieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ))) = 0 := by
    apply sum_eq_zero
    intro t ht
    have hb := (mem_lowerPairs_source.mp (mem_filter.mp ht).1).2.1
    simp only [sourceSieveCount, sieveCount, source_strict_pair_carrier hb, sub_self]
  have hcross := variableS3Main_eq_source_add_correction N w u
  obtain ⟨h10, h11⟩ := jointResidual_source_four_sums_zero N z w V
  unfold finiteElevenExpression
  dsimp only
  rw [hbase z, hbase w, sub_self, sub_self, hsingle, hsingle, hA, hB,
    hpairs, hpairs]
  simp only [sum_sub_distrib]
  unfold variableS3Main sourceVariableS3Main at hcross
  unfold s3FourSourceMajorant s3Upsilon11Source s3FourSourceTerm
  omega

theorem jointResidual_strict_transport_nonpos (N : ℕ) (z w u v V : ℝ) :
    finiteElevenExpression N z w u v V
        (fun d M y => sieveCount N d M y - sourceSieveCount N d M y)
        (fun d y => sourceSieveCount N d (d * N) y - sourceSieveCount N d N y) ≤ 0 := by
  rw [jointResidual_strict_transport]
  have hc : 0 ≤ variableS3CrossingCorrection N w u := by
    apply sum_nonneg
    intro t _
    split_ifs
    · exact sieveCount_nonneg _ _ _ _
    · exact le_rfl
  have hA : 0 ≤ s3FourSourceMajorant N (orderedTriples (primeWindow N z w)) :=
    sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hB : 0 ≤ s3Upsilon11Source N z w V :=
    sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  omega

/-- The actual strict source consumer after evaluating, rather than
bounding absolutely, its signed transport. This is not a payment theorem. -/
theorem jointResidual_strict_consumer {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (finiteElevenUnscaled N z w u v V : ℝ) -
        (variableS3CrossingCorrection N w u : ℝ) -
        (s3FourSourceMajorant N (orderedTriples (primeWindow N z w)) : ℝ) -
        (s3Upsilon11Source N z w V : ℝ) +
        finiteAssemblyGains N z w u v V -
        (s3Upsilon11ExcessMass N z w u V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  have h := finiteElevenExpression_le_count_signed_paid hN he hκ₁ hκ hupper hparam hz
    (sourceSieveCount N) (fun d y => sourceSieveCount N d N y)
  dsimp only at h ⊢
  rw [jointResidual_strict_transport] at h
  push_cast at h
  change _ ≤ _
  unfold finiteElevenUnscaled
  linarith

end Wu2008DoubleSieve
