import MathlibNt.Wu2008DoubleSieve.S3CarrierMajorant

/-!
# Paid repeated-first-prime terms and the Upsilon11 moving range

Wu08 Lemma 2.2, final Delta2 display: the repeated first prime in the
four-factor Buchstab remainder is counted with its full triple
multiplicity. This module does not edit the previously verified carrier
identities or treat their whole-carrier crossing correction as small.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem s3_repeated_first_mem_square {N a b c p : ℕ} {z : ℝ}
    (ha : a.Prime) (hza : z ≤ (a : ℝ)) (hn : 0 < N - p)
    (hp : p ∈ sieveCarrier N (a * b * c * a) N (a : ℝ)) :
    N - p ∈ largePrimeSquareExceptions N z := by
  have hd := (mem_filter.mp hp).2.2.1
  have haa : a ^ 2 ∣ a * b * c * a := by
    have he : a * b * c * a = a ^ 2 * (b * c) := by ring
    rw [he]
    exact dvd_mul_right _ _
  exact mem_largePrimeSquareExceptions.mpr
    ⟨hn, Nat.sub_le N p, a, ha, hza, haa.trans hd⟩

/-- Every surviving triple has three large prime divisors of the actual
positive complement. The cubic multiplicity is not suppressed. -/
theorem s3_repeated_first_multiplicity_le {N p : ℕ} {κ v : ℝ}
    (hN : 1 < N) (hn : 0 < N - p) (hκ : 0 < κ)
    (T : Finset (ℕ × ℕ × ℕ))
    (hT : T ⊆ orderedTriples (primeWindow N ((N : ℝ) ^ κ) v)) :
    ((T.filter (fun t => p ∈
      sieveCarrier N (t.1 * t.2.1 * t.2.2 * t.1) N (t.1 : ℝ))).card : ℝ) ≤
        (1 / κ) ^ 3 := by
  let F := largePrimeDivisors (N - p) ((N : ℝ) ^ κ)
  have hs : T.filter (fun t => p ∈
      sieveCarrier N (t.1 * t.2.1 * t.2.2 * t.1) N (t.1 : ℝ)) ⊆
        F ×ˢ (F ×ˢ F) := by
    rintro ⟨a, b, c⟩ ht
    obtain ⟨ht, hp⟩ := mem_filter.mp ht
    obtain ⟨ha, _, hza, hb, _, hc, _, _, hab, hbc⟩ :=
      mem_s3_ordered_triples.mp (hT ht)
    have hd := (mem_filter.mp hp).2.2.1
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
    have had : a ∣ N - p := (dvd_mul_left a (a * b * c)).trans hd
    have hbd : b ∣ N - p :=
      ((dvd_mul_left b a).trans (dvd_mul_right (a * b) (c * a))).trans (by
        simpa only [mul_assoc] using hd)
    have hcd : c ∣ N - p :=
      ((dvd_mul_left c (a * b)).trans (dvd_mul_right (a * b * c) a)).trans hd
    exact mem_product.mpr
      ⟨mem_largePrimeDivisors.mpr ⟨ha, had, hn.ne', hza⟩,
        mem_product.mpr
          ⟨mem_largePrimeDivisors.mpr ⟨hb, hbd, hn.ne', hza.trans hab'⟩,
            mem_largePrimeDivisors.mpr ⟨hc, hcd, hn.ne', (hza.trans hab').trans hbc'⟩⟩⟩
  have hc : (F.card : ℝ) ≤ 1 / κ :=
    largePrimeDivisors_card_le_inv hN hn (Nat.sub_le N p) hκ
  calc
    _ ≤ ((F ×ˢ (F ×ˢ F)).card : ℝ) := by exact_mod_cast card_le_card hs
    _ = (F.card : ℝ) ^ 3 := by simp only [card_product, Nat.cast_mul]; ring
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 3

/-- Actual repeated-first-prime mass is paid uniformly in the upper
cutoff and in every subfamily of its triple carrier. -/
theorem s3_repeated_first_mass_le {N : ℕ} {κ v : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ)
    (T : Finset (ℕ × ℕ × ℕ))
    (hT : T ⊆ orderedTriples (primeWindow N ((N : ℝ) ^ κ) v)) :
    (s3RepeatedFirstPrimeMass N T : ℝ) ≤
      2 * (1 / κ) ^ 3 * (N : ℝ) ^ (1 - κ) := by
  let E := (primeIndices N).filter
    (fun p => N - p ∈ largePrimeSquareExceptions N ((N : ℝ) ^ κ))
  let f := fun t : ℕ × ℕ × ℕ =>
    sieveCarrier N (t.1 * t.2.1 * t.2.2 * t.1) N (t.1 : ℝ)
  have hf : ∀ t ∈ T, f t ⊆ E := by
    rintro ⟨a, b, c⟩ ht p hp
    obtain ⟨hpR, hpp, _⟩ := mem_filter.mp hp
    have hpN : p ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hpR
    obtain ⟨ha, _, hza, _⟩ := mem_s3_ordered_triples.mp (hT ht)
    exact mem_filter.mpr ⟨mem_primeIndices.mpr ⟨hpN, hpp⟩,
      s3_repeated_first_mem_square ha hza
        (complement_pos_of_even hN he hpN hpp) hp⟩
  have hmass : (s3RepeatedFirstPrimeMass N T : ℝ) =
      ∑ t ∈ T, ((f t).card : ℝ) := by
    simp only [s3RepeatedFirstPrimeMass, sieveCount, Int.cast_sum, Int.cast_natCast, f]
  rw [hmass, endpoint_sum_cards_eq T E f hf]
  have hcard : (E.card : ℝ) ≤ 2 * (N : ℝ) ^ (1 - κ) := by
    calc
      _ ≤ ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ) := by
        exact_mod_cast primeComplement_filter_card_le N
          (largePrimeSquareExceptions N ((N : ℝ) ^ κ))
      _ ≤ _ := largePrimeSquareExceptions_card_le_rpow (by omega) hz
  calc
    _ ≤ ∑ _p ∈ E, (1 / κ) ^ 3 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hpp⟩ := mem_primeIndices.mp (mem_filter.mp hp).1
      exact s3_repeated_first_multiplicity_le (by omega)
        (complement_pos_of_even hN he hpN hpp) hκ T hT
    _ = (E.card : ℝ) * (1 / κ) ^ 3 := by simp
    _ ≤ (2 * (N : ℝ) ^ (1 - κ)) * (1 / κ) ^ 3 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- Disjointness pays the two actual Delta2 triple ranges together:
there is one cubic multiplicity budget, not two independent budgets. -/
theorem s3_repeated_first_two_ranges_le {N : ℕ} {κ w u : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ)
    (hwu : w ≤ u) :
    (s3RepeatedFirstPrimeMass N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ) w)) : ℝ) +
      (s3RepeatedFirstPrimeMass N (s3SecondRange N ((N : ℝ) ^ κ) w u) : ℝ) ≤
        2 * (1 / κ) ^ 3 * (N : ℝ) ^ (1 - κ) := by
  have hdis := (s3_delta_ranges_disjoint N ((N : ℝ) ^ κ) w u).1
  have h := s3_repeated_first_mass_le hN he hκ hz
    (orderedTriples (primeWindow N ((N : ℝ) ^ κ) w) ∪
      s3SecondRange N ((N : ℝ) ^ κ) w u)
    (union_subset (s3_ordered_triples_mono N _ hwu) (filter_subset _ _))
  simpa only [s3RepeatedFirstPrimeMass, sum_union hdis, Int.cast_add] using h

/-- The previously unpaid repeated-first-prime terms in the finite
source Delta2 theorem now have an explicit power-saving budget. -/
theorem s3_delta2_ge_source_fourprime_paid {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    -(s3FourSourceMajorant N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂))) : ℝ) -
      (s3FourSourceMajorant N
        (s3SecondRange N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
          ((N : ℝ) ^ (1 / 2 - 3 * κ₁))) : ℝ) -
      2 * (1 / κ₁) ^ 3 * (N : ℝ) ^ (1 - κ₁) ≤
      (s3Delta2Quotient N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
        ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) := by
  have h := s3_delta2_ge_source_fourprime_add_repeated (by omega : 1 ≤ N)
    hκ₁ hκ hupper hparam
  have hwu : (N : ℝ) ^ κ₂ ≤ (N : ℝ) ^ (1 / 2 - 3 * κ₁) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by linarith : κ₂ ≤ 1 / 2 - 3 * κ₁)
  have hR := s3_repeated_first_two_ranges_le hN he (by linarith : 0 < κ₁) hz hwu
  have hc := (Int.cast_le (R := ℝ)).mpr h
  push_cast at hc
  linarith

/-- The exact Upsilon11 index range, with strict moving upper cutoff
`d < V/c`. For the paper use `V = N^(1/2-2*κ₁)`. -/
noncomputable def s3Upsilon11Range (N : ℕ) (z w V : ℝ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  (orderedTriples (primeWindow N z w)).biUnion (fun t =>
    (primeWindow N w (V / t.2.2)).image (fun d => (t.1, t.2.1, t.2.2, d)))

theorem mem_s3Upsilon11Range {N a b c d : ℕ} {z w V : ℝ} :
    (a, b, c, d) ∈ s3Upsilon11Range N z w V ↔
      a.Prime ∧ a.Coprime N ∧ z ≤ (a : ℝ) ∧
      b.Prime ∧ b.Coprime N ∧ c.Prime ∧ c.Coprime N ∧
      d.Prime ∧ d.Coprime N ∧ a < b ∧ b < c ∧
      (c : ℝ) < w ∧ w ≤ (d : ℝ) ∧ (d : ℝ) < V / c := by
  simp only [s3Upsilon11Range, mem_biUnion, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x, y, r⟩, ht, s, hs, hxa, hyb, hrc, hsd⟩
    dsimp at hxa hyb hrc
    subst x; subst y; subst r; subst s
    obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hcw, hab, hbc⟩ :=
      mem_s3_ordered_triples.mp ht
    obtain ⟨hd, hdN, hwd, hdV⟩ := mem_primeWindow.mp hs
    exact ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hab, hbc, hcw, hwd, hdV⟩
  · rintro ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hab, hbc, hcw, hwd, hdV⟩
    exact ⟨(a, b, c), mem_s3_ordered_triples.mpr
      ⟨ha, haN, hza, hb, hbN, hc, hcN, hcw, hab, hbc⟩,
      d, mem_primeWindow.mpr ⟨hd, hdN, hwd, hdV⟩, rfl, rfl, rfl, rfl⟩

/-- No tuple multiplicity is lost by forming the moving-range union. -/
theorem sum_s3Upsilon11Range (N : ℕ) (z w V : ℝ)
    (f : ℕ × ℕ × ℕ × ℕ → ℤ) :
    ∑ t ∈ s3Upsilon11Range N z w V, f t =
      ∑ t ∈ orderedTriples (primeWindow N z w),
        ∑ d ∈ primeWindow N w (V / t.2.2), f (t.1, t.2.1, t.2.2, d) := by
  unfold s3Upsilon11Range
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro t _
    apply sum_image
    intro c _ d _ h
    exact congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.2) h
  · intro t _ r _ htr
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨c, _, hc⟩ := mem_image.mp hx
    obtain ⟨d, _, hd⟩ := mem_image.mp hy
    have he := hc.trans hd.symm
    exact htr (Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.1) he)
      (Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.1) he)
        (congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.1) he)))

theorem s3Upsilon11_mem_iff_of_second {N a b c d : ℕ} {z w u V : ℝ}
    (ht : (a, b, c, d) ∈ s3DistinctQuadruples N (s3SecondRange N z w u)) :
    (a, b, c, d) ∈ s3Upsilon11Range N z w V ↔ (c : ℝ) * d < V := by
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, _, hab, hbc, _, hcw, hwd⟩ :=
    mem_s3_second_quadruples.mp ht
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  constructor
  · intro h
    have hdV := (mem_s3Upsilon11Range.mp h).2.2.2.2.2.2.2.2.2.2.2.2.2
    simpa only [mul_comm] using (lt_div_iff₀ hc0).mp hdV
  · intro h
    exact mem_s3Upsilon11Range.mpr
      ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hab, hbc, hcw, hwd,
        (lt_div_iff₀ hc0).mpr (by simpa only [mul_comm] using h)⟩

noncomputable def s3Upsilon11Excess (N : ℕ) (z w u V : ℝ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  (s3DistinctQuadruples N (s3SecondRange N z w u)).filter
    (fun t => V ≤ (t.2.2.1 : ℝ) * t.2.2.2)

/-- The target cutoff is strict. Its equality boundary belongs to the
excess, not to the moving Upsilon11 range. -/
theorem s3Upsilon11Excess_eq_sdiff (N : ℕ) (z w u V : ℝ) :
    s3Upsilon11Excess N z w u V =
      s3DistinctQuadruples N (s3SecondRange N z w u) \ s3Upsilon11Range N z w V := by
  ext ⟨a, b, c, d⟩
  simp only [s3Upsilon11Excess, mem_filter, mem_sdiff]
  constructor
  · rintro ⟨ht, hV⟩
    exact ⟨ht, fun hm => (not_lt_of_ge hV) ((s3Upsilon11_mem_iff_of_second ht).mp hm)⟩
  · rintro ⟨ht, hm⟩
    exact ⟨ht, le_of_not_gt (fun hV => hm ((s3Upsilon11_mem_iff_of_second ht).mpr hV))⟩

/-- Mere range inclusion cannot justify the printed transition.
These cutoffs are those of `N=2^32`, `κ₁=1/16`, `κ₂=1/8`;
the tuple `(5,7,13,317)` lies in the actual excess. This says nothing
about possible cancellation in a larger weighted inequality. -/
theorem s3Upsilon11_numeric_range_noninclusion :
    ¬s3DistinctQuadruples (2 ^ 32) (s3SecondRange (2 ^ 32) 4 16 1024) ⊆
      s3Upsilon11Range (2 ^ 32) 4 16 4096 := by
  intro hsub
  have ht : (5, 7, 13, 317) ∈
      s3DistinctQuadruples (2 ^ 32) (s3SecondRange (2 ^ 32) 4 16 1024) := by
    rw [mem_s3_second_quadruples]
    norm_num
  have h := (s3Upsilon11_mem_iff_of_second ht).mp (hsub ht)
  norm_num at h

noncomputable def s3FourSourceTerm (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  sourceSieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)
    ((t.1 * t.2.1 * t.2.2.1 * t.2.2.2) * N) (t.2.1 : ℝ)

noncomputable def s3Upsilon11Source (N : ℕ) (z w V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Range N z w V, s3FourSourceTerm N t

noncomputable def s3Upsilon11ExcessMass (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Excess N z w u V, s3FourSourceTerm N t

/-- An exact finite comparison: the rectangular second range and the
moving range differ by their two genuine, nonnegative carrier sums. -/
theorem s3_second_source_eq_moving_add_excess_sub_missing (N : ℕ) (z w u V : ℝ) :
    s3FourSourceMajorant N (s3SecondRange N z w u) =
      s3Upsilon11Source N z w V + s3Upsilon11ExcessMass N z w u V -
        ∑ t ∈ s3Upsilon11Range N z w V \
          s3DistinctQuadruples N (s3SecondRange N z w u), s3FourSourceTerm N t := by
  let A := s3DistinctQuadruples N (s3SecondRange N z w u)
  let B := s3Upsilon11Range N z w V
  have hA := sum_sdiff (f := s3FourSourceTerm N) (inter_subset_left (s₁ := A) (s₂ := B))
  have hB := sum_sdiff (f := s3FourSourceTerm N) (inter_subset_right (s₁ := A) (s₂ := B))
  have hEA : A \ (A ∩ B) = A \ B := by ext t; simp
  have hEB : B \ (A ∩ B) = B \ A := by ext t; simp
  rw [hEA] at hA
  rw [hEB] at hB
  unfold s3Upsilon11ExcessMass
  rw [s3Upsilon11Excess_eq_sdiff]
  change (∑ t ∈ A, s3FourSourceTerm N t) =
    (∑ t ∈ B, s3FourSourceTerm N t) + (∑ t ∈ A \ B, s3FourSourceTerm N t) -
      (∑ t ∈ B \ A, s3FourSourceTerm N t)
  omega

theorem s3_second_source_le_moving_add_excess (N : ℕ) (z w u V : ℝ) :
    s3FourSourceMajorant N (s3SecondRange N z w u) ≤
      s3Upsilon11Source N z w V + s3Upsilon11ExcessMass N z w u V := by
  rw [s3_second_source_eq_moving_add_excess_sub_missing]
  apply sub_le_self
  exact sum_nonneg (fun _ _ => Int.natCast_nonneg _)

/-- Positive complements inject into the exact finite set of positive
multiples. This remains valid for `d=0` and arbitrary real cutoffs. -/
theorem s3_source_count_le_positive_multiples {N : ℕ}
    (hN : 4 ≤ N) (he : Even N) (d M : ℕ) (z : ℝ) :
    sourceSieveCount N d M z ≤ (N / d : ℕ) := by
  unfold sourceSieveCount
  apply Int.ofNat_le.mpr
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card_of_injOn (fun p => N - p)
  · intro p hp
    obtain ⟨hpR, hpp, hd, _⟩ := mem_filter.mp hp
    have hpN : p ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hpR
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨complement_pos_of_even hN he hpN hpp, Nat.sub_le N p⟩, hd⟩
  · intro p hp q hq h
    have hpN : p ≤ N := by
      simpa only [mem_range, Nat.lt_succ_iff] using (mem_filter.mp hp).1
    have hqN : q ≤ N := by
      simpa only [mem_range, Nat.lt_succ_iff] using (mem_filter.mp hq).1
    dsimp at h
    omega

/-- A proved floor-count budget for the entire excess. No assertion
that this budget is `O(N^(1-κ₁))` is made. -/
noncomputable def s3Upsilon11ExcessMultipleBudget (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Excess N z w u V,
    (N / (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) : ℕ)

theorem s3Upsilon11ExcessMass_le_multiple_budget {N : ℕ}
    (hN : 4 ≤ N) (he : Even N) (z w u V : ℝ) :
    s3Upsilon11ExcessMass N z w u V ≤ s3Upsilon11ExcessMultipleBudget N z w u V := by
  apply sum_le_sum
  intro t _
  exact s3_source_count_le_positive_multiples hN he _ _ _

theorem s3_second_source_le_moving_add_multiple_budget {N : ℕ}
    (hN : 4 ≤ N) (he : Even N) (z w u V : ℝ) :
    s3FourSourceMajorant N (s3SecondRange N z w u) ≤
      s3Upsilon11Source N z w V + s3Upsilon11ExcessMultipleBudget N z w u V := by
  exact (s3_second_source_le_moving_add_excess N z w u V).trans
    (add_le_add le_rfl (s3Upsilon11ExcessMass_le_multiple_budget hN he z w u V))

/-- Delta2 with the actual printed Upsilon11 index cutoff, source
`P(d*N)` carriers, paid repeated terms, and the remaining explicit
positive-multiple budget. This does not discard the excess. -/
theorem s3_delta2_ge_moving_fourprime_with_budget {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    -(s3FourSourceMajorant N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂))) : ℝ) -
      (s3Upsilon11Source N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
        ((N : ℝ) ^ (1 / 2 - 2 * κ₁)) : ℝ) -
      (s3Upsilon11ExcessMultipleBudget N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
        ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 2 - 2 * κ₁)) : ℝ) -
      2 * (1 / κ₁) ^ 3 * (N : ℝ) ^ (1 - κ₁) ≤
      (s3Delta2Quotient N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
        ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) := by
  have h := s3_delta2_ge_source_fourprime_paid hN he hκ₁ hκ hupper hparam hz
  have hm := s3_second_source_le_moving_add_multiple_budget hN he
    ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂) ((N : ℝ) ^ (1 / 2 - 3 * κ₁))
    ((N : ℝ) ^ (1 / 2 - 2 * κ₁))
  have hmc := (Int.cast_le (R := ℝ)).mpr hm
  push_cast at hmc
  linarith

end Wu2008DoubleSieve
