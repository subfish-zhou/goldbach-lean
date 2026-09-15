import MathlibNt.SieveTheory.LiLiuPrereqWFTagCardinality

/-!
# The exponential bound for the actual normalized signed family

Bernoulli's inequality gives the coarser alphabet size `⌊ε⁻¹¹⌋ + 1`,
which is already sufficient without the logarithmic grid-count estimate.
The elementary inequality `log t ≤ t / 2` then absorbs this alphabet
and the length bound into `exp (8 ε⁻³)`.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open scoped Classical

namespace TagCardinality

theorem log_le_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 2 := by
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hhalf := Real.log_le_sub_one_of_pos (by positivity : 0 < t / 2)
  rw [Real.log_div (ne_of_gt ht) (by norm_num)] at hhalf
  linarith

theorem uniformBound_lt_exp {t : ℝ} (ht : 1 ≤ t) :
    (((⌊t ^ 11⌋₊ + 2) ^ ⌊t ^ 2⌋₊ : ℕ) : ℝ) < Real.exp (8 * t ^ 3) := by
  have htpos : 0 < t := by linarith
  have hone : 1 ≤ t ^ 11 := one_le_pow₀ ht
  have hbase : (⌊t ^ 11⌋₊ : ℝ) + 2 ≤ 3 * t ^ 11 := by
    have hf := Nat.floor_le (pow_nonneg htpos.le 11)
    linarith
  have hbasepos : 0 < (⌊t ^ 11⌋₊ : ℝ) + 2 := by positivity
  have hlogbase : Real.log ((⌊t ^ 11⌋₊ : ℝ) + 2) ≤ 2 + 11 * (t / 2) := by
    have hm := Real.log_le_log hbasepos hbase
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt (pow_pos htpos 11)),
      Real.log_pow] at hm
    have hthree := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have hhalf := log_le_half htpos
    norm_num only [Nat.cast_ofNat] at hm
    linarith
  have hlognonneg : 0 ≤ Real.log ((⌊t ^ 11⌋₊ : ℝ) + 2) := by
    apply Real.log_nonneg
    have hn : (0 : ℝ) ≤ ⌊t ^ 11⌋₊ := Nat.cast_nonneg _
    linarith
  have hR : (⌊t ^ 2⌋₊ : ℝ) ≤ t ^ 2 := Nat.floor_le (sq_nonneg t)
  have hlog :
      (⌊t ^ 2⌋₊ : ℝ) * Real.log ((⌊t ^ 11⌋₊ : ℝ) + 2) < 8 * t ^ 3 := by
    calc
      (⌊t ^ 2⌋₊ : ℝ) * Real.log ((⌊t ^ 11⌋₊ : ℝ) + 2) ≤
          t ^ 2 * (2 + 11 * (t / 2)) :=
        mul_le_mul hR hlogbase hlognonneg (sq_nonneg t)
      _ < t ^ 2 * (8 * t) :=
        mul_lt_mul_of_pos_left (by linarith) (sq_pos_of_pos htpos)
      _ = 8 * t ^ 3 := by ring
  apply (Real.log_lt_iff_lt_exp (by positivity)).mp
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Real.log_pow] using hlog

end TagCardinality

/-- The actual accepted profiles, including the empty profile, satisfy the
source exponential family-size bound. Neither correct geometric labelling nor
a cardinality premise is needed, and the estimate is uniform in `P` and `D`. -/
theorem signedTags_card_lt_exp (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 1 < D) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ((signedTags upper P D ε label).card : ℝ) < Real.exp (8 * (ε⁻¹) ^ 3) := by
  have ht : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hεone
  exact lt_of_le_of_lt (by exact_mod_cast signedTags_card_le_uniform upper P label hD hε)
    (TagCardinality.uniformBound_lt_exp ht)

/-- The source range `D ≥ 2`, `0 < ε < 1/8` is an immediate specialization. -/
theorem signedTags_card_lt_exp_source (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    ((signedTags upper P D ε label).card : ℝ) < Real.exp (8 * (ε⁻¹) ^ 3) :=
  signedTags_card_lt_exp upper P label (by linarith) hε (by linarith)

#check signedTags_card_lt_exp
#print axioms signedTags_card_lt_exp
#check signedTags_card_lt_exp_source
#print axioms signedTags_card_lt_exp_source

end MathlibNt.SieveTheory.LiLiuPrereqWF
