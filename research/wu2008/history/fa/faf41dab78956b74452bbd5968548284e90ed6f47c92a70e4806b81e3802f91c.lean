import MathlibNt.Wu2008DoubleSieve.NinthProductProfile

/-!
# Whole-support geometry at the final ninth-term parameters

Every product in the mother support satisfies the balanced interval
conditions. No prime in its fibre, nor any prime output, is assumed.
The explicit threshold 512 is proved using rational power comparisons.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def ninthProfileK1 : ℝ := 100 / 1327
noncomputable def ninthProfileK2 : ℝ := 25 / 206
noncomputable def ninthProfileSigma : ℝ := 1 / 2 - 3 * ninthProfileK1
noncomputable def ninthProfileW (N : ℕ) : ℝ := (N : ℝ) ^ ninthProfileK2
noncomputable def ninthProfileU (N : ℕ) : ℝ := (N : ℝ) ^ ninthProfileSigma
noncomputable def ninthProductSupport (N : ℕ) : Finset ℕ :=
  M9 N (ninthProfileW N) (ninthProfileU N)

/-- An exact rational-power evaluation, not a numerical scan. -/
theorem ninth_rpow_512 (r : ℝ) :
    (512 : ℝ) ^ (r / 9) = (2 : ℝ) ^ r := by
  calc
    (512 : ℝ) ^ (r / 9) = ((2 : ℝ) ^ (9 : ℝ)) ^ (r / 9) := by norm_num
    _ = (2 : ℝ) ^ ((9 : ℝ) * (r / 9)) :=
      (Real.rpow_mul (by norm_num) _ _).symm
    _ = _ := by congr 1; ring

theorem ninth_fixed_cutoffs_ge {N : ℕ} (hN : 512 ≤ N) :
    2 ≤ ninthProfileW N ∧ 4 ≤ ninthProfileU N := by
  have h512 : (512 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · calc
      (2 : ℝ) = (512 : ℝ) ^ (1 / 9 : ℝ) := by
        rw [ninth_rpow_512]; norm_num
      _ ≤ (N : ℝ) ^ (1 / 9 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) h512 (by norm_num)
      _ ≤ ninthProfileW N :=
        Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by norm_num [ninthProfileK2])
  · calc
      (4 : ℝ) = (512 : ℝ) ^ (2 / 9 : ℝ) := by
        rw [ninth_rpow_512]; norm_num
      _ ≤ (N : ℝ) ^ (2 / 9 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) h512 (by norm_num)
      _ ≤ ninthProfileU N :=
        Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by norm_num [ninthProfileSigma, ninthProfileK1])

theorem ninth_fixed_lower_ge_two {N : ℕ} (hN : 512 ≤ N) :
    2 ≤ ninthProfileLower (ninthProfileU N) := by
  have hu := (ninth_fixed_cutoffs_ge hN).2
  have hc := Int.le_ceil (ninthProfileU N)
  simp only [ninthProfileLower, Int.cast_sub, Int.cast_one]
  linarith

/-- The source pair-size inequality controls the product square before
any restriction on the varying prime or its output is imposed. -/
theorem ninthPair_product_sq_lt {N : ℕ} {w u : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ ninthPairs N w u) :
    (ninthPairProduct t : ℝ) ^ 2 < (N : ℝ) * u := by
  obtain ⟨hpair, hau⟩ := mem_filter.mp ht
  obtain ⟨ha, _, _, _, _, _, hsize⟩ := mem_lowerPairs_source.mp hpair
  have hs : (t.1 : ℝ) * t.2 ^ 2 < N := by
    exact_mod_cast (lower_pair_size_iff ha.pos).mpr hsize
  have haR : (0 : ℝ) < t.1 := by exact_mod_cast ha.pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast ninthPair_N_pos ht
  calc
    (ninthPairProduct t : ℝ) ^ 2 = (t.1 : ℝ) * ((t.1 : ℝ) * t.2 ^ 2) := by
      simp only [ninthPairProduct, Nat.cast_mul]
      ring
    _ < (t.1 : ℝ) * N := mul_lt_mul_of_pos_left hs haR
    _ < u * N := mul_lt_mul_of_pos_right hau hNR
    _ = _ := by ring

theorem ninthProductSupport_balanced {N m : ℕ} (hN : 512 ≤ N)
    (hm : m ∈ ninthProductSupport N) :
    (N : ℝ) ^ ninthProfileK2 ≤ m ∧
      (m : ℝ) ≤ (N : ℝ) ^ (1 - ninthProfileK2) := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  obtain ⟨ha, hb, _, hwa, _, _, _⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp ht).1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  constructor
  · have hb1 : (1 : ℝ) ≤ t.2 := by exact_mod_cast hb.one_lt.le
    calc
      (N : ℝ) ^ ninthProfileK2 ≤ t.1 := hwa
      _ ≤ (t.1 : ℝ) * t.2 :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) hb1
      _ = _ := by simp only [ninthPairProduct, Nat.cast_mul]
  · have hp := ninthPair_product_sq_lt ht
    have he : (N : ℝ) * ninthProfileU N ≤
        ((N : ℝ) ^ (1 - ninthProfileK2)) ^ 2 := by
      calc
        (N : ℝ) * ninthProfileU N =
            (N : ℝ) ^ (1 + ninthProfileSigma) := by
          rw [Real.rpow_add hNR, Real.rpow_one]
          rfl
        _ ≤ (N : ℝ) ^ ((1 - ninthProfileK2) * 2) :=
          Real.rpow_le_rpow_of_exponent_le hN1
            (by norm_num [ninthProfileK2, ninthProfileSigma, ninthProfileK1])
        _ = ((N : ℝ) ^ (1 - ninthProfileK2)) ^ 2 := by
          rw [Real.rpow_mul hNR.le]
          norm_num
    have hpos := Real.rpow_nonneg hNR.le (1 - ninthProfileK2)
    nlinarith

/-- The integer lower endpoint is feasible throughout the mother support.
Integer multiplication upgrades the strict size bound to `m*L <= N-1`. -/
theorem ninthPair_profile_interval {N : ℕ} {w u : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ ninthPairs N w u) :
    ninthProfileLower u ≤ ninthProfileUpper N (ninthPairProduct t) ∧
      (ninthPairProduct t : ℝ) * ninthProfileUpper N (ninthPairProduct t) ≤ N := by
  obtain ⟨ha, _, _, _, hub, _, hsize⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp ht).1
  have hm : (0 : ℝ) < ninthPairProduct t := by
    exact_mod_cast ninthPair_product_pos ht
  have hs : (ninthPairProduct t : ℝ) * t.2 < N := by
    have h := (lower_pair_size_iff ha.pos).mpr hsize
    have h' : ninthPairProduct t * t.2 < N := by
      simpa only [ninthPairProduct, pow_two, mul_assoc] using h
    exact_mod_cast h'
  have hml : (ninthPairProduct t : ℝ) * ninthProfileLower u < N :=
    (mul_lt_mul_of_pos_left ((ninthProfileLower_lt u).trans_le hub) hm).trans hs
  have hi : (ninthPairProduct t : ℤ) * ((⌈u⌉ : ℤ) - 1) < (N : ℤ) := by
    unfold ninthProfileLower at hml
    exact_mod_cast hml
  have hi' : (ninthPairProduct t : ℤ) * ((⌈u⌉ : ℤ) - 1) ≤ (N : ℤ) - 1 := by
    omega
  have hr : (ninthPairProduct t : ℝ) * ninthProfileLower u ≤ (N : ℝ) - 1 := by
    unfold ninthProfileLower
    exact_mod_cast hi'
  constructor
  · apply (le_div_iff₀ hm).mpr
    simpa only [mul_comm] using hr
  · have heq : (ninthPairProduct t : ℝ) *
        ninthProfileUpper N (ninthPairProduct t) = (N : ℝ) - 1 := by
      unfold ninthProfileUpper
      field_simp
    linarith

/-- All hypotheses needed by the existing balanced-distribution consumer,
uniformly for every support product and without an output hypothesis. -/
theorem ninthProductSupport_geometry {N : ℕ} (hN : 512 ≤ N)
    (m : ℕ) (hm : m ∈ ninthProductSupport N) :
    (N : ℝ) ^ ninthProfileK2 ≤ m ∧
      (m : ℝ) ≤ (N : ℝ) ^ (1 - ninthProfileK2) ∧
      2 ≤ ninthProfileLower (ninthProfileU N) ∧
      ninthProfileLower (ninthProfileU N) ≤ ninthProfileUpper N m ∧
      (m : ℝ) * ninthProfileUpper N m ≤ N := by
  obtain ⟨hlo, hhi⟩ := ninthProductSupport_balanced hN hm
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  exact ⟨hlo, hhi, ninth_fixed_lower_ge_two hN, ninthPair_profile_interval ht⟩

end Wu2008DoubleSieve
