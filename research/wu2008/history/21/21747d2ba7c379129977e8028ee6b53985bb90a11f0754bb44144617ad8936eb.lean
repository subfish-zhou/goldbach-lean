import R2MotherCountPrefix
import R2MotherMovingRange

namespace WuPaper.R2Mother

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def paperTriple (N : ℕ) (t : ℕ × ℕ × ℕ) : ℤ :=
  sieveCount N (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ)

noncomputable def paperDelta2 (N : ℕ) (z w u v : ℝ) : ℤ :=
  (∑ t ∈ orderedTriples (primeWindow N z v), paperTriple N t) - delta1 N z w u

noncomputable def paperRetained (N : ℕ) (z w u v : ℝ) : ℤ :=
  (∑ t ∈ orderedTriples (primeWindow N z v) \
      (orderedTriples (primeWindow N z w) ∪ s3SecondRange N z w u ∪ s3ThirdRange N w u),
    paperTriple N t) +
  ∑ t ∈ s3ThirdRange N w u,
    (paperTriple N t - sieveCount N (t.1 * t.2.1 * t.2.2) N (t.2.2 : ℝ))

noncomputable def thirdModulusLoss (N : ℕ) (w u : ℝ) : ℤ :=
  ∑ t ∈ s3ThirdRange N w u,
    (sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.2 : ℝ) -
      sieveCount N (t.1 * t.2.1 * t.2.2) N (t.2.2 : ℝ))

theorem paperRetained_nonneg (N : ℕ) (z w u v : ℝ) :
    0 ≤ paperRetained N z w u v := by
  apply add_nonneg
  · exact sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _)
  · apply sum_nonneg
    intro t ht
    apply sub_nonneg.mpr
    exact sieveCount_antitone N _ _
      (by exact_mod_cast (mem_s3ThirdRange.mp ht).2.2.2.le)

theorem paperDelta2_le_delta2 (N : ℕ) (z w u v : ℝ) :
    paperDelta2 N z w u v ≤ delta2 N z w u v := by
  apply sub_le_sub_right
  apply sum_le_sum
  intro t _
  exact s3_sieveCount_le_mul_modulus N _ N t.1 _

theorem paper_eq26_count {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    (firstNine N z w u v + paperDelta2 N z w u v : ℤ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  have h := eq26_count hN he hκ₁ hκ hupper hz
  dsimp only at h ⊢
  have hm := (Int.cast_le (R := ℝ)).mpr
    (paperDelta2_le_delta2 N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
      ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 3 : ℝ)))
  push_cast at h ⊢
  linarith

theorem modulus_loss_le_repeated (N d a : ℕ) {y : ℝ}
    (ha : a.Prime) (haN : a.Coprime N) (hay : (a : ℝ) ≤ y) :
    sieveCount N d (N * a) y - sieveCount N d N y ≤
      sieveCount N (d * a) N (a : ℝ) := by
  have h := sieveCount_mul_modulus_eq_add_loss N d N a y ha haN
  have hs :
      (sieveCarrier N d (N * a) y).filter
        (fun p => (a : ℝ) < y ∧ a ∣ (N - p) / d) ⊆
        sieveCarrier N (d * a) N (a : ℝ) := by
    intro p hp
    obtain ⟨hp, _, had⟩ := mem_filter.mp hp
    obtain ⟨hpR, hpp, hd, hsift⟩ := mem_filter.mp hp
    have hda : d * a ∣ N - p := (Nat.dvd_div_iff_mul_dvd hd).mp had
    refine mem_filter.mpr ⟨hpR, hpp, hda, ?_⟩
    intro q hq hqN hqa hqd
    have hqa' : q ≠ a := by
      intro h
      subst q
      exact (lt_irrefl (a : ℝ)) hqa
    have hqNa : q.Coprime (N * a) :=
      Nat.coprime_mul_iff_right.mpr ⟨hqN, (Nat.coprime_primes hq ha).mpr hqa'⟩
    have hqold : q ∣ (N - p) / d := by
      rw [← Nat.div_div_eq_div_mul] at hqd
      exact hqd.trans (Nat.div_dvd_of_dvd had)
    exact hsift q hq hqNa (hqa.trans_le hay) hqold
  have hc : (((sieveCarrier N d (N * a) y).filter
      (fun p => (a : ℝ) < y ∧ a ∣ (N - p) / d)).card : ℤ) ≤
      sieveCount N (d * a) N (a : ℝ) := by
    unfold sieveCount
    exact_mod_cast card_le_card hs
  omega

theorem thirdModulusLoss_le_repeated (N : ℕ) (w u : ℝ) :
    thirdModulusLoss N w u ≤ s3RepeatedFirstPrimeMass N (s3ThirdRange N w u) := by
  apply sum_le_sum
  rintro ⟨a, b, c⟩ ht
  obtain ⟨hpair, _, _, hbc⟩ := mem_s3ThirdRange.mp ht
  obtain ⟨ha, _, hcop, _, _, hab, _⟩ := mem_lowerPairs_source.mp hpair
  exact modulus_loss_le_repeated N (a * b * c) a ha
    (Nat.coprime_mul_iff_left.mp hcop).1 (by exact_mod_cast (hab.trans hbc).le)

theorem paper_delta2_exact (N : ℕ) (z w u v : ℝ)
    (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    paperDelta2 N z w u v =
      paperRetained N z w u v - thirdModulusLoss N w u -
        (∑ t ∈ orderedTriples (primeWindow N z w), s3FourPrimeRemainder N t) -
        ∑ t ∈ s3SecondRange N z w u, s3FourPrimeRemainder N t := by
  let A := orderedTriples (primeWindow N z w)
  let B := s3SecondRange N z w u
  let C := s3ThirdRange N w u
  let T := orderedTriples (primeWindow N z v)
  obtain ⟨hAB, hAC, hBC⟩ := s3_delta_ranges_disjoint N z w u
  have hsub : A ∪ B ∪ C ⊆ T :=
    union_subset (union_subset (s3_ordered_triples_mono N z hwv)
      ((filter_subset _ _).trans (s3_ordered_triples_mono N z huv))) hthird
  have hsum := sum_sdiff (f := paperTriple N) hsub
  rw [sum_union (disjoint_union_left.mpr ⟨hAC, hBC⟩), sum_union hAB] at hsum
  have hA : (∑ t ∈ A,
      sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ)) =
      (∑ t ∈ A, paperTriple N t) + ∑ t ∈ A, s3FourPrimeRemainder N t := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    have h := s3_triple_cutoff_difference N t.1 t.2.1 t.2.2
      (mem_s3_ordered_triples.mp ht).2.2.2.2.2.2.2.2.1.le
    change _ - paperTriple N t = s3FourPrimeRemainder N t at h
    omega
  have hB : (∑ t ∈ B,
      sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ)) =
      (∑ t ∈ B, paperTriple N t) + ∑ t ∈ B, s3FourPrimeRemainder N t := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    have h := s3_triple_cutoff_difference N t.1 t.2.1 t.2.2
      (mem_s3_ordered_triples.mp (mem_filter.mp ht).1).2.2.2.2.2.2.2.2.1.le
    change _ - paperTriple N t = s3FourPrimeRemainder N t at h
    omega
  unfold paperDelta2 delta1 firstTriple secondTriple paperRetained thirdModulusLoss
  rw [variableS3Triples_eq_third_range_sum]
  simp only [sum_sub_distrib]
  dsimp only [A, B, C, T] at hsum hA hB
  omega

theorem paper_delta2_moving_exact (N : ℕ) {z w u v V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    paperDelta2 N z w u v + upsilon10 N z w + upsilon11 N z w V =
      paperRetained N z w u v - quotientExcess N z w u V -
        s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) -
        s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) -
        thirdModulusLoss N w u := by
  have hA := s3_fourprime_sum_split N (orderedTriples (primeWindow N z w)) (by
    intro t ht
    obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ := mem_s3_ordered_triples.mp ht
    exact ⟨ha, haN, hab⟩)
  have hB := s3_fourprime_sum_split N (s3SecondRange N z w u) (by
    intro t ht
    obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ :=
      mem_s3_ordered_triples.mp (mem_filter.mp ht).1
    exact ⟨ha, haN, hab⟩)
  have hq := rectangle_quotient_sum N (w := w) hu hV
  have hd := paper_delta2_exact N z w u v hwv huv hthird
  change _ = upsilon10 N z w + s3RepeatedFirstPrimeMass N _ at hA
  change _ = (∑ t ∈ s3DistinctQuadruples N (s3SecondRange N z w u),
    fourQuotientTerm N t) + s3RepeatedFirstPrimeMass N _ at hB
  omega

theorem three_ranges_repeated_paid {N : ℕ} {κ w u v : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ)
    (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆
      orderedTriples (primeWindow N ((N : ℝ) ^ κ) v)) :
    (s3RepeatedFirstPrimeMass N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ) w)) : ℝ) +
      (s3RepeatedFirstPrimeMass N (s3SecondRange N ((N : ℝ) ^ κ) w u) : ℝ) +
      (thirdModulusLoss N w u : ℝ) ≤
        2 * (1 / κ) ^ 3 * (N : ℝ) ^ (1 - κ) := by
  obtain ⟨hAB, hAC, hBC⟩ := s3_delta_ranges_disjoint N ((N : ℝ) ^ κ) w u
  have h := s3_repeated_first_mass_le hN he hκ hz
    (orderedTriples (primeWindow N ((N : ℝ) ^ κ) w) ∪
      s3SecondRange N ((N : ℝ) ^ κ) w u ∪ s3ThirdRange N w u)
    (union_subset (union_subset (s3_ordered_triples_mono N _ hwv)
      ((filter_subset _ _).trans (s3_ordered_triples_mono N _ huv))) hthird)
  have ht := (Int.cast_le (R := ℝ)).mpr (thirdModulusLoss_le_repeated N w u)
  simp only [s3RepeatedFirstPrimeMass,
    sum_union (disjoint_union_left.mpr ⟨hAC, hBC⟩), sum_union hAB, Int.cast_add] at h
  unfold s3RepeatedFirstPrimeMass at ht ⊢
  linarith

theorem original_delta2_signed_paid {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁);
    -(upsilon10 N z w : ℝ) - (upsilon11 N z w V : ℝ) +
      (paperRetained N z w u v : ℝ) - (quotientExcess N z w u V : ℝ) -
      2 * (1 / κ₁) ^ 3 * (N : ℝ) ^ (1 - κ₁) ≤ (paperDelta2 N z w u v : ℝ) := by
  dsimp only
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwv := Real.rpow_le_rpow_of_exponent_le hN1
    (show κ₂ ≤ 1 / 3 by linarith)
  have huv := Real.rpow_le_rpow_of_exponent_le hN1
    (show 1 / 2 - 3 * κ₁ ≤ 1 / 3 by linarith)
  have hthird := s3ThirdRange_subset_source_triples (by omega : 1 ≤ N) hκ hparam
  have hd := congrArg (fun x : ℤ => (x : ℝ))
    (paper_delta2_moving_exact N (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (source_cutoff_product (by omega : 0 < N) κ₁).le hwv huv hthird)
  have hp := three_ranges_repeated_paid hN he (by linarith : 0 < κ₁) hz hwv huv hthird
  push_cast at hd
  linarith

theorem original_eleven_count_frontier {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (eleven N z w u v V : ℝ) + (paperRetained N z w u v : ℝ) -
      (quotientExcess N z w u V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  have hc := paper_eq26_count hN he hκ₁ hκ hupper hz
  have hd := original_delta2_signed_paid hN he hκ₁ hκ hupper hparam hz
  dsimp only at hc hd ⊢
  rw [eleven_eq_firstNine]
  push_cast at hc ⊢
  nlinarith

end WuPaper.R2Mother

#check @WuPaper.R2Mother.paperTriple
#check @WuPaper.R2Mother.paperDelta2
#check @WuPaper.R2Mother.paperRetained
#check @WuPaper.R2Mother.thirdModulusLoss
#check @WuPaper.R2Mother.paperRetained_nonneg
#check @WuPaper.R2Mother.paperDelta2_le_delta2
#check @WuPaper.R2Mother.paper_eq26_count
#check @WuPaper.R2Mother.modulus_loss_le_repeated
#check @WuPaper.R2Mother.thirdModulusLoss_le_repeated
#check @WuPaper.R2Mother.paper_delta2_exact
#check @WuPaper.R2Mother.paper_delta2_moving_exact
#check @WuPaper.R2Mother.three_ranges_repeated_paid
#check @WuPaper.R2Mother.original_delta2_signed_paid
#check @WuPaper.R2Mother.original_eleven_count_frontier
#print axioms WuPaper.R2Mother.paperTriple
#print axioms WuPaper.R2Mother.paperDelta2
#print axioms WuPaper.R2Mother.paperRetained
#print axioms WuPaper.R2Mother.thirdModulusLoss
#print axioms WuPaper.R2Mother.paperRetained_nonneg
#print axioms WuPaper.R2Mother.paperDelta2_le_delta2
#print axioms WuPaper.R2Mother.paper_eq26_count
#print axioms WuPaper.R2Mother.modulus_loss_le_repeated
#print axioms WuPaper.R2Mother.thirdModulusLoss_le_repeated
#print axioms WuPaper.R2Mother.paper_delta2_exact
#print axioms WuPaper.R2Mother.paper_delta2_moving_exact
#print axioms WuPaper.R2Mother.three_ranges_repeated_paid
#print axioms WuPaper.R2Mother.original_delta2_signed_paid
#print axioms WuPaper.R2Mother.original_eleven_count_frontier
