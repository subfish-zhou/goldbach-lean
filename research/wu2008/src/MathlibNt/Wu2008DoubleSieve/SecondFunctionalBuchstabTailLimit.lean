import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabTailSlope

/-! Finite unit-block contraction, followed by completeness, for the actual Buchstab function. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Real Filter LiLiuPrereqBuchstab

lemma buchstab_increment_nat (m : ℕ) (hm : 3 ≤ m) {x y : ℝ}
    (hx : (m : ℝ) ≤ x) (hy : (m : ℝ) ≤ y) :
    |buchstab y - buchstab x| ≤ (2 / (m.factorial : ℝ)) * |y - x| := by
  have he : m - 3 + 3 = m := by omega
  have hc : ((m - 3 : ℕ) : ℝ) + 3 = (m : ℝ) := by exact_mod_cast he
  simpa only [he] using buchstab_tail_increment (m - 3) (hc ▸ hx) (hc ▸ hy)

lemma factorial_tail_budget (m : ℕ) (hm : 3 ≤ m) :
    2 / (m.factorial : ℝ) + 4 / ((m + 1).factorial : ℝ) ≤
      4 / (m.factorial : ℝ) := by
  have hf : (0 : ℝ) < m.factorial := by positivity
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  apply (le_div_iff₀ hf).2
  field_simp
  nlinarith

/-- Every finite interval is controlled without retaining its length. -/
lemma buchstab_finite_tail (n m : ℕ) (hm : 3 ≤ m) {x y : ℝ}
    (hx : (m : ℝ) ≤ x) (hxy : x ≤ y) (hy : y ≤ (m : ℝ) + n) :
    |buchstab y - buchstab x| ≤ 4 / (m.factorial : ℝ) := by
  induction n generalizing m x y with
  | zero =>
    have he : y = x := by simp only [Nat.cast_zero, add_zero] at hy; linarith
    rw [he, sub_self, abs_zero]
    positivity
  | succ n ih =>
    by_cases hy1 : y ≤ (m : ℝ) + 1
    · have hb := buchstab_increment_nat m hm hx (hx.trans hxy)
      have hd : |y - x| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hxy)]; linarith
      have hp : 0 ≤ 2 / (m.factorial : ℝ) := by positivity
      calc
        _ ≤ (2 / (m.factorial : ℝ)) * |y - x| := hb
        _ ≤ (2 / (m.factorial : ℝ)) * 1 := mul_le_mul_of_nonneg_left hd hp
        _ ≤ 4 / (m.factorial : ℝ) := by
          rw [mul_one]
          exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    · have hy' : y ≤ ((m + 1 : ℕ) : ℝ) + n := by push_cast at hy ⊢; linarith
      by_cases hx1 : ((m + 1 : ℕ) : ℝ) ≤ x
      · exact (ih (m + 1) (by omega) hx1 hxy hy').trans
          (by
            have h := factorial_tail_budget m hm
            have hp : 0 ≤ 2 / (m.factorial : ℝ) := by positivity
            linarith)
      · have hx1' : x ≤ ((m + 1 : ℕ) : ℝ) := le_of_not_ge hx1
        have hb := buchstab_increment_nat m hm hx
          (show (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) by push_cast; linarith)
        have hd : |((m + 1 : ℕ) : ℝ) - x| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hx1')]; push_cast; linarith
        have hfirst : |buchstab ((m + 1 : ℕ) : ℝ) - buchstab x| ≤
            2 / (m.factorial : ℝ) :=
          hb.trans (by
            have hp : 0 ≤ 2 / (m.factorial : ℝ) := by positivity
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hp)
        have hrest := ih (m + 1) (by omega) (le_refl ((m + 1 : ℕ) : ℝ))
          (show ((m + 1 : ℕ) : ℝ) ≤ y by push_cast; linarith) hy'
        calc
          _ ≤ |buchstab y - buchstab ((m + 1 : ℕ) : ℝ)| +
              |buchstab ((m + 1 : ℕ) : ℝ) - buchstab x| := abs_sub_le _ _ _
          _ ≤ 4 / ((m + 1).factorial : ℝ) + 2 / (m.factorial : ℝ) := add_le_add hrest hfirst
          _ ≤ 4 / (m.factorial : ℝ) := by linarith [factorial_tail_budget m hm]

/-- Uniform oscillation on the entire real half-line. -/
theorem buchstab_tail_oscillation (m : ℕ) (hm : 3 ≤ m) :
    ∀ x : ℝ, (m : ℝ) ≤ x → ∀ y : ℝ, (m : ℝ) ≤ y →
      |buchstab y - buchstab x| ≤ 4 / (m.factorial : ℝ) := by
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm]
    exact this y hy x hx (le_of_not_ge hxy)
  obtain ⟨n, hn⟩ := exists_nat_ge (y - m)
  exact buchstab_finite_tail n m hm hx hxy (by linarith)

/-- A single integer threshold makes the factorial budget arbitrarily small. -/
lemma exists_factorial_tail_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 3 ≤ m ∧ 4 / (m.factorial : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / ε)
  refine ⟨n + 3, by omega, ?_⟩
  have hf : (0 : ℝ) < (n + 3).factorial := by positivity
  have hnf : ((n + 3 : ℕ) : ℝ) ≤ (n + 3).factorial :=
    by exact_mod_cast Nat.self_le_factorial (n + 3)
  have hlt : 4 / ε < ((n + 3 : ℕ) : ℝ) := by push_cast; linarith
  exact (div_lt_iff₀ hf).2 (by
    have h := (div_lt_iff₀ hε).1 (hlt.trans_le hnf)
    nlinarith)

/-- The actual Buchstab function is Cauchy on the real filter at infinity. -/
theorem buchstab_cauchy_atTop : Cauchy (Filter.map buchstab (atTop : Filter ℝ)) := by
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨m, hm, hsmall⟩ := exists_factorial_tail_threshold hε
  refine ⟨(m : ℝ), ?_⟩
  intro x hx y hy
  rw [Real.dist_eq]
  exact (buchstab_tail_oscillation m hm y hy x hx).trans_lt hsmall

/-- Existence is produced from the proved finite-block bounds and completeness. -/
theorem exists_buchstab_tail_limit : ∃ L : ℝ, Tendsto buchstab atTop (nhds L) :=
  cauchy_map_iff_exists_tendsto.mp buchstab_cauchy_atTop

/-- The limit selected only after proving existence for the actual function. -/
noncomputable def buchstabTailLimit : ℝ := exists_buchstab_tail_limit.choose

theorem tendsto_buchstab_tail_limit : Tendsto buchstab atTop (nhds buchstabTailLimit) :=
  exists_buchstab_tail_limit.choose_spec

theorem buchstab_tail_limit_unique {L : ℝ} (hL : Tendsto buchstab atTop (nhds L)) :
    L = buchstabTailLimit := tendsto_nhds_unique hL tendsto_buchstab_tail_limit

theorem existsUnique_buchstab_tail_limit : ∃! L : ℝ, Tendsto buchstab atTop (nhds L) :=
  ⟨buchstabTailLimit, tendsto_buchstab_tail_limit, fun _ h => buchstab_tail_limit_unique h⟩

/-- The requested factorial error, uniform in every real point beyond the threshold. -/
theorem buchstab_tail_limit_error (m : ℕ) (hm : 3 ≤ m) :
    ∀ u : ℝ, (m : ℝ) ≤ u → |buchstab u - buchstabTailLimit| ≤ 4 / (m.factorial : ℝ) := by
  intro u hu
  apply le_of_tendsto ((tendsto_const_nhds.sub tendsto_buchstab_tail_limit).abs)
  filter_upwards [eventually_ge_atTop (m : ℝ)] with y hy
  exact buchstab_tail_oscillation m hm y hy u hu

theorem buchstab_tail_limit_bounds : 1 / 2 ≤ buchstabTailLimit ∧ buchstabTailLimit ≤ 1 := by
  constructor
  · apply ge_of_tendsto tendsto_buchstab_tail_limit
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    exact one_half_le_buchstab hu
  · apply le_of_tendsto tendsto_buchstab_tail_limit
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    exact buchstab_le_one hu

end Wu2008DoubleSieve.SecondFunctionalJointTail
