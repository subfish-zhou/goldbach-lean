import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaDecay

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- An explicit threshold beyond which the source cutoff is at least three. -/
theorem exists_sourceSigma_three_threshold (d : ℝ) (hd : 0 < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D → 3 ≤ sourceSigma D d := by
  let D0 : ℝ := Real.exp (Real.exp 3)
  have hD0 : 1 < D0 := Real.one_lt_exp_iff.mpr (Real.exp_pos 3)
  refine ⟨D0, hD0, ?_⟩
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos (Real.exp 3)).trans_le hD
  have hx : Real.exp 3 ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 hD
  have hxone : 1 ≤ Real.log D := by
    have : 1 ≤ Real.exp 3 := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hpow : 1 ≤ (Real.log D) ^ (1 / d) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hxone
        (by positivity : 0 ≤ 1 / d)
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner : Real.exp 3 ≤ Real.log (27 * D) := by
    rw [hlog27D]
    have hlog27 : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
    linarith
  have hll : 3 ≤ Real.log (Real.log (27 * D)) := by
    rw [← Real.log_exp 3]
    exact Real.log_le_log (Real.exp_pos 3) hinner
  unfold sourceSigma
  nlinarith [mul_nonneg (sub_nonneg.mpr hpow) (sub_nonneg.mpr hll)]

/-- Once `σ ≥ 3`, increasing the denominator of the exponent decreases the
power of a base at least one. -/
theorem sourceSigma_rpow_le_cubeRoot
    {D d : ℝ} (hD : 1 ≤ D) (hσ : 3 ≤ sourceSigma D d) :
    D ^ (1 / sourceSigma D d) ≤ D ^ (1 / 3 : ℝ) := by
  have hσpos : 0 < sourceSigma D d := lt_of_lt_of_le (by norm_num) hσ
  have hexp : 1 / sourceSigma D d ≤ 1 / (3 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hσ
  exact Real.rpow_le_rpow_of_exponent_le hD hexp

/-- Explicit eventual lower bound `2 ≤ D^(1/σ(D))`.  The assumption `1 < d`
is essential to this proof: `log D / σ(D)` then grows like a positive power of
`log D` divided by `log log D`. -/
theorem exists_two_le_rpow_inv_sourceSigma_threshold
    (d : ℝ) (hd : 1 < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      2 ≤ D ^ (1 / sourceSigma D d) := by
  let a : ℝ := (1 - 1 / d) / 2
  have hd0 : 0 < d := zero_lt_one.trans hd
  have ha : 0 < a := by
    dsimp [a]
    have hrecip := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hd
    have : 1 / d < 1 := by norm_num at hrecip ⊢; exact hrecip
    linarith
  let C : ℝ := max 1 (2 * Real.log 2 / a)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  let X : ℝ := max 2 (max (Real.log 27) (C ^ (1 / a)))
  have hX2 : 2 ≤ X := le_max_left _ _
  have hXpos : 0 < X := by linarith
  refine ⟨Real.exp X, Real.one_lt_exp_iff.mpr hXpos, ?_⟩
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hD
  have hxX : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hD
  let x : ℝ := Real.log D
  have hx2 : 2 ≤ x := hX2.trans hxX
  have hxpos : 0 < x := by linarith
  have hlog27x : Real.log 27 ≤ x := by
    exact ((le_max_left (Real.log 27) (C ^ (1 / a))).trans
      (le_max_right 2 _)).trans hxX
  have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner_le : Real.log (27 * D) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinner_pos : 0 < Real.log (27 * D) := by
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hll_le : Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := by
    have h := Real.strictMonoOn_log.monotoneOn hinner_pos
      (show 0 < 2 * x by positivity) hinner_le
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h
    have hlog2 : Real.log 2 ≤ Real.log x :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx2
    linarith
  have hlogx : Real.log x ≤ x ^ a / a := Real.log_le_rpow_div hxpos.le ha
  have hll_bound : Real.log (Real.log (27 * D)) ≤ (2 / a) * x ^ a := by
    calc
      _ ≤ 2 * Real.log x := hll_le
      _ ≤ 2 * (x ^ a / a) := mul_le_mul_of_nonneg_left hlogx (by norm_num)
      _ = (2 / a) * x ^ a := by ring
  have hCroot : C ^ (1 / a) ≤ x := by
    exact ((le_max_right (Real.log 27) (C ^ (1 / a))).trans
      (le_max_right 2 _)).trans hxX
  have hCa : C ≤ x ^ a := by
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg hCpos.le _) hCroot ha.le
    have hp : (C ^ (1 / a)) ^ a = C := by
      rw [← Real.rpow_mul hCpos.le]
      have : (1 / a) * a = 1 := by field_simp
      rw [this, Real.rpow_one]
    rwa [hp] at hr
  have htargeta : 2 * Real.log 2 / a ≤ x ^ a :=
    (le_max_right (1 : ℝ) _).trans hCa
  have hllpos : 0 < Real.log (Real.log (27 * D)) := by
    apply Real.log_pos
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hsigpos : 0 < sourceSigma D d := by
    unfold sourceSigma
    exact mul_pos (Real.rpow_pos_of_pos hxpos _) hllpos
  have hexponents : 1 / d + a + a = 1 := by
    dsimp [a]
    ring
  have hlog2sigma : Real.log 2 * sourceSigma D d ≤ x := by
    unfold sourceSigma
    have hnonneg : 0 ≤ Real.log 2 * x ^ (1 / d) := by positivity
    calc
      Real.log 2 * (x ^ (1 / d) * Real.log (Real.log (27 * D))) ≤
          Real.log 2 * (x ^ (1 / d) * ((2 / a) * x ^ a)) := by
            gcongr
      _ = (2 * Real.log 2 / a) * (x ^ (1 / d) * x ^ a) := by ring
      _ ≤ x ^ a * (x ^ (1 / d) * x ^ a) := by gcongr
      _ = x := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        have he : a + (1 / d + a) = 1 := by linarith [hexponents]
        rw [he, Real.rpow_one]
  have hquot : Real.log 2 ≤ Real.log D / sourceSigma D d := by
    rw [le_div_iff₀ hsigpos]
    simpa [x, mul_comm] using hlog2sigma
  rw [Real.rpow_def_of_pos hDpos]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr (by simpa [div_eq_mul_inv] using hquot)

/-- The three moving geometric size premises share one explicit threshold. -/
theorem exists_sourceSigma_geometry_threshold (d : ℝ) (hd : 1 < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      3 ≤ sourceSigma D d ∧
      D ^ (1 / sourceSigma D d) ≤ D ^ (1 / 3 : ℝ) ∧
      2 ≤ D ^ (1 / sourceSigma D d) := by
  obtain ⟨D3, hD3, hthree⟩ := exists_sourceSigma_three_threshold d (zero_lt_one.trans hd)
  obtain ⟨D2, hD2, htwo⟩ := exists_two_le_rpow_inv_sourceSigma_threshold d hd
  let D0 := max D3 D2
  refine ⟨D0, hD3.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have h3D : D3 ≤ D := (le_max_left _ _).trans hD
  have h2D : D2 ≤ D := (le_max_right _ _).trans hD
  have hDone : 1 ≤ D := (le_of_lt hD3).trans h3D
  exact ⟨hthree D h3D, sourceSigma_rpow_le_cubeRoot hDone (hthree D h3D), htwo D h2D⟩

/-- A natural cubic cutoff gives the required upper real cube-root inequality;
it does not give equality unless `D` is a perfect cube. -/
theorem cubeRoot_le_of_nat_cubic_upper {D y : ℕ} (hyUpper : D ≤ y ^ 3) :
    (D : ℝ) ^ (1 / 3 : ℝ) ≤ (y : ℝ) := by
  have hcast : (D : ℝ) ≤ (y : ℝ) ^ (3 : ℕ) := by exact_mod_cast hyUpper
  have hnonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hy0 : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
  have := Real.rpow_le_rpow hnonneg hcast (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc
    (D : ℝ) ^ (1 / 3 : ℝ) ≤ ((y : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := this
    _ = (y : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]
      norm_num

/-- The strict lower cubic bracket places the predecessor below the real cube root. -/
theorem nat_pred_lt_cubeRoot_of_cubic_lower {D y : ℕ} (hyLower : (y - 1) ^ 3 < D) :
    ((y - 1 : ℕ) : ℝ) < (D : ℝ) ^ (1 / 3 : ℝ) := by
  have hcast : (((y - 1 : ℕ) : ℝ) ^ (3 : ℕ)) < (D : ℝ) := by exact_mod_cast hyLower
  have hbase0 : 0 ≤ (((y - 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hcub0 : 0 ≤ (((y - 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by positivity
  have h := Real.rpow_lt_rpow hcub0 hcast (by norm_num : (0 : ℝ) < 1 / 3)
  calc
    ((y - 1 : ℕ) : ℝ) = ((((y - 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0]
      norm_num
    _ < (D : ℝ) ^ (1 / 3 : ℝ) := h

/-- A cubic upper bracket and `D ≥ 8` force the natural cutoff to be at least two. -/
theorem two_le_nat_cutoff_of_cubic_upper {D y : ℕ}
    (hD8 : 8 ≤ D) (hyUpper : D ≤ y ^ 3) : 2 ≤ y := by
  by_contra h
  have hy : y ≤ 1 := by omega
  interval_cases y <;> norm_num at hyUpper <;> omega

/-- The natural bracket also yields the real `y ≤ D/2` premise for `D ≥ 8`. -/
theorem nat_cutoff_le_half_of_cubic_lower {D y : ℕ}
    (hD8 : 8 ≤ D) (hyLower : (y - 1) ^ 3 < D)
    (hyUpper : D ≤ y ^ 3) :
    (y : ℝ) ≤ (D : ℝ) / 2 := by
  have hy2 : 2 ≤ y := two_le_nat_cutoff_of_cubic_upper hD8 hyUpper
  by_cases hy : y = 2
  · subst y
    have hD8R : (8 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD8
    norm_num
    linarith
  have hy3 : 3 ≤ y := by omega
  have hcubic : (y - 1) ^ 3 + 1 ≤ D := by omega
  have halg : 2 * y ≤ (y - 1) ^ 3 + 1 := by
    let t : ℝ := ((y - 1 : ℕ) : ℝ)
    have ht2 : 2 ≤ t := by
      dsimp [t]
      exact_mod_cast (show 2 ≤ y - 1 by omega)
    have hpoly : 2 * (t + 1) ≤ t ^ 3 + 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht2) (sq_nonneg (t + 1))]
    have hyt : (y : ℝ) = t + 1 := by
      dsimp [t]
      rw [Nat.cast_sub (by omega : 1 ≤ y)]
      norm_num
    have halgR : 2 * (y : ℝ) ≤ ((y - 1 : ℕ) : ℝ) ^ 3 + 1 := by
      calc
        2 * (y : ℝ) = 2 * (t + 1) := by rw [hyt]
        _ ≤ t ^ 3 + 1 := hpoly
        _ = ((y - 1 : ℕ) : ℝ) ^ 3 + 1 := by rfl
    exact_mod_cast halgR
  have h2y : 2 * y ≤ D := halg.trans hcubic
  have h2yR : (2 : ℝ) * (y : ℝ) ≤ (D : ℝ) := by exact_mod_cast h2y
  linarith

/-- All real inequalities genuinely supplied by the natural cubic bracket.
The casts are explicit, so this packet cannot be confused with a real-valued
choice of `y` or with `⌈D^(1/3)⌉₊`. -/
theorem nat_cubic_cutoff_real_geometry {D y : ℕ}
    (hD8 : 8 ≤ D) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3) :
    ((y - 1 : ℕ) : ℝ) < (D : ℝ) ^ (1 / 3 : ℝ) ∧
    (D : ℝ) ^ (1 / 3 : ℝ) ≤ (y : ℝ) ∧
    2 ≤ (y : ℝ) ∧ (y : ℝ) ≤ (D : ℝ) / 2 := by
  refine ⟨nat_pred_lt_cubeRoot_of_cubic_lower hyLower,
    cubeRoot_le_of_nat_cubic_upper hyUpper, ?_,
    nat_cutoff_le_half_of_cubic_lower hD8 hyLower hyUpper⟩
  exact_mod_cast two_le_nat_cutoff_of_cubic_upper hD8 hyUpper

/-- One common eventual threshold supplies the source-`σ` geometry and all
valid consequences of a natural cubic cutoff. -/
theorem exists_sourceSigma_and_nat_cubic_geometry_threshold
    (d : ℝ) (hd : 1 < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ (D y : ℕ), D0 ≤ (D : ℝ) →
      (y - 1) ^ 3 < D → D ≤ y ^ 3 →
      3 ≤ sourceSigma (D : ℝ) d ∧
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤
        (D : ℝ) ^ (1 / 3 : ℝ) ∧
      2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ∧
      ((y - 1 : ℕ) : ℝ) < (D : ℝ) ^ (1 / 3 : ℝ) ∧
      (D : ℝ) ^ (1 / 3 : ℝ) ≤ (y : ℝ) ∧
      2 ≤ (y : ℝ) ∧ (y : ℝ) ≤ (D : ℝ) / 2 := by
  obtain ⟨Dσ, hDσ, hσ⟩ := exists_sourceSigma_geometry_threshold d hd
  let D0 : ℝ := max Dσ 8
  refine ⟨D0, hDσ.trans_le (le_max_left _ _), ?_⟩
  intro D y hD hyLower hyUpper
  have hDσD : Dσ ≤ (D : ℝ) := (le_max_left Dσ 8).trans hD
  have hD8R : (8 : ℝ) ≤ (D : ℝ) := (le_max_right Dσ 8).trans hD
  have hD8 : 8 ≤ D := by exact_mod_cast hD8R
  obtain ⟨hthree, hroot, htwo⟩ := hσ (D : ℝ) hDσD
  obtain ⟨hpred, hcube, hy2, hyhalf⟩ :=
    nat_cubic_cutoff_real_geometry hD8 hyLower hyUpper
  exact ⟨hthree, hroot, htwo, hpred, hcube, hy2, hyhalf⟩

/-- Adversarial audit: the natural cubic bracket does **not** imply the exact
identity `D^(1/3)=y` demanded by the current raw Case-II theorem.  The pair
`D=2, y=2` is already a counterexample. -/
theorem nat_cubic_bracket_does_not_force_cubeRoot_eq :
    ∃ D y : ℕ, (y - 1) ^ 3 < D ∧ D ≤ y ^ 3 ∧
      (D : ℝ) ^ (1 / 3 : ℝ) ≠ (y : ℝ) := by
  refine ⟨2, 2, by norm_num, by norm_num, ?_⟩
  have hlt : (2 : ℝ) ^ (1 / 3 : ℝ) < (8 : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    calc
      (8 : ℝ) ^ (1 / 3 : ℝ) = (((2 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) := by norm_num
      _ = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  rw [h8] at hlt
  exact ne_of_lt hlt


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
