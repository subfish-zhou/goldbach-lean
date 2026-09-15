import WR2MotherTerms

namespace WuPaper.R2Mother

open Finset Wu2008DoubleSieve
open scoped Classical

theorem moving_subset_rectangle (N : ℕ) {z w u V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) :
    s3Upsilon11Range N z w V ⊆
      s3DistinctQuadruples N (s3SecondRange N z w u) := by
  rintro ⟨a, b, c, d⟩ ht
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN,
    hab, hbc, hcw, hwd, hdV⟩ := mem_s3Upsilon11Range.mp ht
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have hac : (a : ℝ) < c := by exact_mod_cast hab.trans hbc
  have hzc : z ≤ (c : ℝ) := hza.trans hac.le
  have hprod : (d : ℝ) * c < V := (lt_div_iff₀ hc0).mp hdV
  have hcu : z * u ≤ (c : ℝ) * u := mul_le_mul_of_nonneg_right hzc hu
  have hdu : (d : ℝ) < u := by nlinarith
  have hcd : c < d := by exact_mod_cast hcw.trans_le hwd
  exact mem_s3_second_quadruples.mpr
    ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hdu, hab, hbc, hcd, hcw, hwd⟩

theorem missingMass_zero (N : ℕ) {z w u V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) :
    s3Upsilon11MissingMass N z w u V = 0 := by
  unfold s3Upsilon11MissingMass
  rw [sdiff_eq_empty_iff_subset.mpr (moving_subset_rectangle N hu hV), sum_empty]

theorem source_cutoff_product {N : ℕ} (hN : 0 < N) (κ : ℝ) :
    (N : ℝ) ^ (1 / 2 - 2 * κ) =
      (N : ℝ) ^ κ * (N : ℝ) ^ (1 / 2 - 3 * κ) := by
  rw [← Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]
  congr 1
  ring

theorem source_moving_subset_rectangle {N : ℕ} (hN : 0 < N) (κ₁ κ₂ : ℝ) :
    s3Upsilon11Range N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
        ((N : ℝ) ^ (1 / 2 - 2 * κ₁)) ⊆
      s3DistinctQuadruples N (s3SecondRange N ((N : ℝ) ^ κ₁)
        ((N : ℝ) ^ κ₂) ((N : ℝ) ^ (1 / 2 - 3 * κ₁))) :=
  moving_subset_rectangle N (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (source_cutoff_product hN κ₁).le

theorem source_missingMass_zero {N : ℕ} (hN : 0 < N) (κ₁ κ₂ : ℝ) :
    s3Upsilon11MissingMass N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
      ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 2 - 2 * κ₁)) = 0 :=
  missingMass_zero N (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (source_cutoff_product hN κ₁).le

noncomputable def quotientExcess (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Excess N z w u V, fourQuotientTerm N t

noncomputable def movingModulusGain (N : ℕ) (z w V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Range N z w V, (s3FourSourceTerm N t - fourQuotientTerm N t)

theorem quotientExcess_nonneg (N : ℕ) (z w u V : ℝ) :
    0 ≤ quotientExcess N z w u V :=
  sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _)

theorem movingModulusGain_nonneg (N : ℕ) (z w V : ℝ) :
    0 ≤ movingModulusGain N z w V :=
  sum_nonneg (fun _ _ => sub_nonneg.mpr (sieveCount_le_source_selected_modulus N _ N _))

theorem rectangle_quotient_sum (N : ℕ) {z w u V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) :
    (∑ t ∈ s3DistinctQuadruples N (s3SecondRange N z w u), fourQuotientTerm N t) =
      upsilon11 N z w V + quotientExcess N z w u V := by
  have h := sum_sdiff (f := fourQuotientTerm N) (moving_subset_rectangle N (w := w) hu hV)
  unfold quotientExcess upsilon11
  rw [s3Upsilon11Excess_eq_sdiff]
  omega

theorem rectangle_modulus_cancellation (N : ℕ) {z w u V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) :
    s3FourModulusGain N (s3SecondRange N z w u) -
      s3Upsilon11ExcessMass N z w u V =
      movingModulusGain N z w V - quotientExcess N z w u V := by
  have hs := s3_second_source_eq_moving_add_excess_sub_missing N z w u V
  change _ = _ + _ - s3Upsilon11MissingMass N z w u V at hs
  rw [missingMass_zero N hu hV] at hs
  have hq := rectangle_quotient_sum N (w := w) hu hV
  unfold s3FourModulusGain movingModulusGain
  simp only [sum_sub_distrib]
  change s3FourSourceMajorant N (s3SecondRange N z w u) - _ - _ =
    s3Upsilon11Source N z w V - upsilon11 N z w V - _
  change _ = _ + quotientExcess N z w u V at hq
  unfold fourQuotientTerm at hq
  omega

theorem mixed_to_quotient (N : ℕ) (z w u v V : ℝ) :
    finiteElevenMixed N z w u v V +
      s3FourModulusGain N (orderedTriples (primeWindow N z w)) +
      movingModulusGain N z w V = eleven N z w u v V := by
  unfold finiteElevenMixed finiteElevenExpression eleven
    upsilon1 upsilon2 upsilon3 upsilon4 upsilon5 upsilon6
    upsilon7 upsilon8 upsilon9 upsilon10 upsilon11
    s3FourModulusGain movingModulusGain s3FourSourceTerm fourQuotientTerm
  simp only [sum_sub_distrib]
  ring

noncomputable def quotientAssemblyGains (N : ℕ) (z w u v : ℝ) : ℝ :=
  (s3RetainedTripleMass N z w u v : ℝ) + (positiveS4 N w u : ℝ) +
    (s3VariableSlack N w u : ℝ) +
    lowerWeightOuterSlack N w u + lowerWeightOuterSlack N z v

theorem quotientAssemblyGains_nonneg {N : ℕ} (hN : 0 < N)
    {z w : ℝ} (hz : 2 ≤ z) (hw : 2 ≤ w) (u v : ℝ) :
    0 ≤ quotientAssemblyGains N z w u v := by
  have hR := Int.cast_nonneg (R := ℝ) (s3RetainedTripleMass_nonneg N z w u v)
  have h4 := Int.cast_nonneg (R := ℝ) (positiveS4_nonneg N w u)
  have hS := Int.cast_nonneg (R := ℝ) (s3VariableSlack_nonneg N w u)
  have hW := lowerWeightOuterSlack_nonneg hN hw u
  have hZ := lowerWeightOuterSlack_nonneg hN hz v
  unfold quotientAssemblyGains
  linarith

theorem signed_aggregate_transport (N : ℕ) {z w u v V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) :
    (finiteElevenMixed N z w u v V : ℝ) + finiteAssemblyGains N z w u v V -
      (s3Upsilon11ExcessMass N z w u V : ℝ) =
      (eleven N z w u v V : ℝ) + quotientAssemblyGains N z w u v -
        (quotientExcess N z w u V : ℝ) := by
  have hm := congrArg (fun x : ℤ => (x : ℝ)) (mixed_to_quotient N z w u v V)
  have hc := congrArg (fun x : ℤ => (x : ℝ)) (rectangle_modulus_cancellation N (w := w) hu hV)
  push_cast at hm hc
  unfold finiteAssemblyGains quotientAssemblyGains positiveS4
  rw [missingMass_zero N hu hV]
  push_cast
  linarith

theorem eleven_count_signed {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (eleven N z w u v V : ℝ) + quotientAssemblyGains N z w u v -
      (quotientExcess N z w u V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  have h := finiteElevenMixed_le_count_signed_paid hN he hκ₁ hκ hupper hparam hz
  dsimp only at h ⊢
  rwa [signed_aggregate_transport N (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (source_cutoff_product (by omega : 0 < N) κ₁).le] at h

end WuPaper.R2Mother

#check @WuPaper.R2Mother.moving_subset_rectangle
#check @WuPaper.R2Mother.missingMass_zero
#check @WuPaper.R2Mother.source_cutoff_product
#check @WuPaper.R2Mother.source_moving_subset_rectangle
#check @WuPaper.R2Mother.source_missingMass_zero
#check @WuPaper.R2Mother.quotientExcess
#check @WuPaper.R2Mother.movingModulusGain
#check @WuPaper.R2Mother.quotientExcess_nonneg
#check @WuPaper.R2Mother.movingModulusGain_nonneg
#check @WuPaper.R2Mother.rectangle_quotient_sum
#check @WuPaper.R2Mother.rectangle_modulus_cancellation
#check @WuPaper.R2Mother.mixed_to_quotient
#check @WuPaper.R2Mother.quotientAssemblyGains
#check @WuPaper.R2Mother.quotientAssemblyGains_nonneg
#check @WuPaper.R2Mother.signed_aggregate_transport
#check @WuPaper.R2Mother.eleven_count_signed
#print axioms WuPaper.R2Mother.moving_subset_rectangle
#print axioms WuPaper.R2Mother.missingMass_zero
#print axioms WuPaper.R2Mother.source_cutoff_product
#print axioms WuPaper.R2Mother.source_moving_subset_rectangle
#print axioms WuPaper.R2Mother.source_missingMass_zero
#print axioms WuPaper.R2Mother.quotientExcess
#print axioms WuPaper.R2Mother.movingModulusGain
#print axioms WuPaper.R2Mother.quotientExcess_nonneg
#print axioms WuPaper.R2Mother.movingModulusGain_nonneg
#print axioms WuPaper.R2Mother.rectangle_quotient_sum
#print axioms WuPaper.R2Mother.rectangle_modulus_cancellation
#print axioms WuPaper.R2Mother.mixed_to_quotient
#print axioms WuPaper.R2Mother.quotientAssemblyGains
#print axioms WuPaper.R2Mother.quotientAssemblyGains_nonneg
#print axioms WuPaper.R2Mother.signed_aggregate_transport
#print axioms WuPaper.R2Mother.eleven_count_signed
