import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4LogInduction
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4SiegelDichotomy
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterWeightedSum

noncomputable section
open Set Complex DirichletCharacter
namespace AnalyticNumberTheory.LargeSieve
open TatuzawaMultiplicativeTransfer

/-- A genuine fixed zero gives a lower bound for the same actual residue
whose upper bound costs three logarithms. -/
theorem fourFactor_fixed_zero_residue_lower
    (x y : PrimitiveQuadraticDatum) (hxy : x ≠ y)
    {β : ℝ} (hβ : 7/8 ≤ β) (hβ1 : β < 1)
    (hz : let : NeZero x.modulus := ⟨x.modulus_ne⟩
      x.character.LFunction (β : ℂ) = 0) :
    (1-β) / (2 * ((5000 * ((x.modulus*y.modulus : ℕ) : ℝ)^3)^8)^(1-β)) ≤
      (FourFactorLogInduction_residue x y).re := by
  let : NeZero x.modulus := ⟨x.modulus_ne⟩
  let : NeZero y.modulus := ⟨y.modulus_ne⟩
  let : NeZero (x.modulus*y.modulus) := ⟨Nat.mul_ne_zero x.modulus_ne y.modulus_ne⟩
  let a := changeLevel (dvd_mul_right x.modulus y.modulus) x.character
  let b := changeLevel (dvd_mul_left y.modulus x.modulus) y.character
  have haquad : a^2 = 1 := sq_changeLevel_eq_one _ x.square_eq_one
  have hbquad : b^2 = 1 := sq_changeLevel_eq_one _ y.square_eq_one
  have ha : a ≠ 1 := by
    intro h
    apply x.ne_one
    exact changeLevel_injective (dvd_mul_right x.modulus y.modulus) (by simpa [a] using h)
  have hb : b ≠ 1 := by
    intro h
    apply y.ne_one
    exact changeLevel_injective (dvd_mul_left y.modulus x.modulus) (by simpa [b] using h)
  have hp : a*b ≠ 1 := pairCharacter_ne_one_of_datum_ne x y hxy
  have hab : a ≠ b := by
    intro heq
    apply hp
    rw [heq, ← pow_two, hbquad]
  have hza : a.LFunction (β : ℂ) = 0 :=
    (LFunction_changeLevel_real_eq_zero_iff _ _ (by linarith) (Or.inl x.ne_one)).mpr hz
  exact Bombieri1965Theorem4.twoCharacterResidue_re_lower_bound_of_real_zero
    a b ha hb haquad hbquad hab hβ hβ1 (Or.inl hza)

/-- Uniform elementary log absorption, without any varying cutoff. -/
theorem fourFactor_log_cube_absorption {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 < η) :
    (1 + Real.log Q)^3 ≤ (1 + 6/η)^3 * Q^(η/2) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have he : 0 < η/6 := by positivity
  have hpow : 1 ≤ Q^(η/6) := Real.one_le_rpow hQ he.le
  have hl := Real.log_le_rpow_div hQ0.le he
  have hlin : 1 + Real.log Q ≤ (1+6/η)*Q^(η/6) := calc
    _ ≤ Q^(η/6) + Q^(η/6)/(η/6) := add_le_add hpow hl
    _ = _ := by ring
  have hlog : 0 ≤ 1+Real.log Q := by linarith [Real.log_nonneg hQ]
  calc
    _ ≤ ((1+6/η)*Q^(η/6))^3 := pow_le_pow_left₀ hlog hlin _
    _ = (1+6/η)^3 * Q^(η/2) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hQ0.le]
      congr 1
      congr 1
      ring

/-- The actual eighth-power cutoff costs exactly `24d` in the level.
The remaining half exponent absorbs all three logarithms. -/
theorem fourFactor_denominator_bound {Q η d : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 < η) (hdη : 24*d ≤ η/2) :
    ((5000*Q^3)^8)^d * (1+Real.log Q)^3 ≤
      (5000:ℝ)^(8*d) * (1+6/η)^3 * Q^η := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hid : ((5000*Q^3)^8)^d = (5000:ℝ)^(8*d)*Q^(24*d) := by
    rw [← Real.rpow_natCast_mul (by positivity : (0:ℝ) ≤ 5000*Q^3),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5000) (by positivity),
      ← Real.rpow_natCast_mul hQ0.le]
    congr 1
    congr 1
    ring
  rw [hid]
  calc
    _ ≤ ((5000:ℝ)^(8*d)*Q^(24*d)) * ((1+6/η)^3 * Q^(η/2)) :=
      mul_le_mul_of_nonneg_left (fourFactor_log_cube_absorption hQ hη) (by positivity)
    _ = ((5000:ℝ)^(8*d)*(1+6/η)^3) * Q^(24*d+η/2) := by
      rw [Real.rpow_add hQ0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)) (by positivity)

/-- Fixed-zero extraction, uniform over every distinct primitive quadratic datum.
All constants depend only on the fixed datum, fixed zero and exponent. -/
theorem fourFactor_fixed_zero_value_lower
    (x y : PrimitiveQuadraticDatum) (hxy : x ≠ y)
    {β η : ℝ} (hβ : 7/8 ≤ β) (hβ1 : β < 1) (hη : 0 < η)
    (hdη : 24*(1-β) ≤ η/2)
    (hz : let : NeZero x.modulus := ⟨x.modulus_ne⟩
      x.character.LFunction (β : ℂ) = 0) :
    ((1-β) / (64*(5000:ℝ)^(8*(1-β))*(1+6/η)^3*x.value)) *
      ((x.modulus*y.modulus : ℕ) : ℝ)^(-η) ≤ y.value := by
  let Q : ℝ := (x.modulus*y.modulus : ℕ)
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact_mod_cast Nat.mul_pos x.modulus_pos y.modulus_pos
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hd : 0 < 1-β := sub_pos.mpr hβ1
  have hx := x.value_pos
  have hy := y.value_pos
  have hl := fourFactor_fixed_zero_residue_lower x y hxy hβ hβ1 hz
  have hu := (FourFactorLogInduction_residue_re_pos_and_le x y hxy).2.2
  have hlog : 0 < 1+Real.log Q := by linarith [Real.log_nonneg hQ]
  have hp : 0 < ((5000*Q^3)^8)^(1-β) := by positivity
  have hraw : 1-β ≤ 64 * (((5000*Q^3)^8)^(1-β) * (1+Real.log Q)^3) * x.value*y.value := by
    have hh := (div_le_iff₀ (show 0 < 2*((5000*Q^3)^8)^(1-β) by positivity)).mp (hl.trans hu)
    dsimp [Q] at hh ⊢
    nlinarith only [hh]
  have hden := fourFactor_denominator_bound hQ hη hdη
  have hraw' : 1-β ≤ (64*(5000:ℝ)^(8*(1-β))*(1+6/η)^3*x.value) * Q^η * y.value := by
    calc
      _ ≤ _ := hraw
      _ ≤ 64 * ((5000:ℝ)^(8*(1-β))*(1+6/η)^3*Q^η)*x.value*y.value := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hden (by norm_num)) hx.le) hy.le
      _ = _ := by ring
  have hK : 0 < 64*(5000:ℝ)^(8*(1-β))*(1+6/η)^3*x.value := by positivity
  have hout : (1-β) / ((64*(5000:ℝ)^(8*(1-β))*(1+6/η)^3*x.value) * Q^η) ≤ y.value :=
    (div_le_iff₀ (mul_pos hK (Real.rpow_pos_of_pos hQ0 η))).mpr (by simpa only [mul_comm] using hraw')
  change (1-β)/(64*(5000:ℝ)^(8*(1-β))*(1+6/η)^3*x.value) * Q^(-η) ≤ y.value
  rw [Real.rpow_neg hQ0.le]
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hout

/-- The genuine zero branch gives the raw bound after the already proved
finite-conductor bridge. The cutoff and constant precede `q` and `χ`. -/
theorem fourFactor_raw_lower_of_fixed_zero
    (x : PrimitiveQuadraticDatum) {β η : ℝ}
    (hβ : 7/8 ≤ β) (hβ1 : β < 1) (hη : 0 < η)
    (hdη : 24*(1-β) ≤ η/2)
    (hz : let : NeZero x.modulus := ⟨x.modulus_ne⟩
      x.character.LFunction (β : ℂ) = 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ^2 = 1 → χ ≠ 1 →
        c*(q:ℝ)^(-η) ≤ (χ.LFunction 1).re := by
  apply exists_quadratic_LFunction_one_lower_of_eventual η hη
  let c := ((1-β)/(64*(5000:ℝ)^(8*(1-β))*(1+6/η)^3*x.value)) *
    (x.modulus:ℝ)^(-η)
  have hx := x.value_pos
  have hxm : (0:ℝ) < x.modulus := by exact_mod_cast x.modulus_pos
  have hd : 0 < 1-β := sub_pos.mpr hβ1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨x.modulus+1, c, hc, ?_⟩
  intro q _ χ hq hprim hquad hχ
  let y : PrimitiveQuadraticDatum := ⟨q, NeZero.ne q, χ, hprim, hquad, hχ⟩
  have hxy : x ≠ y := by
    intro h
    have hm : x.modulus = q := congrArg PrimitiveQuadraticDatum.modulus h
    omega
  have hv := fourFactor_fixed_zero_value_lower x y hxy hβ hβ1 hη hdη hz
  change c*(q:ℝ)^(-η) ≤ y.value
  convert hv using 1
  dsimp [c, y]
  rw [Nat.cast_mul, Real.mul_rpow (by positivity : (0:ℝ) ≤ x.modulus)
    (by positivity : (0:ℝ) ≤ q)]
  ring

/-- Unconditional raw Landau--Siegel theorem for every positive exponent.
The only analytic sources are the actual small-value/real-zero dichotomy,
the actual real-zero residue lower bound, and the log-cubed induction upper bound. -/
theorem fourFactor_rawLandauSiegelLowerBound : RawLandauSiegelLowerBound := by
  intro η hη
  obtain ⟨δ, _hδ, hδ8, hδη, hw | hn⟩ := fourFactor_siegel_noZero_or_witness η hη
  · obtain ⟨x, β, hβ, hz⟩ := hw
    exact fourFactor_raw_lower_of_fixed_zero x (by linarith [hβ.1]) hβ.2 hη
      (by linarith [hβ.1]) hz
  · exact hn

/-- Requested headline specialization; no lower-bound source is a hypothesis. -/
theorem fourFactor_raw_siegel_one_over_ten_thousand :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ^2 = 1 → χ ≠ 1 →
        c*(q:ℝ)^(-(1/10000:ℝ)) ≤ (χ.LFunction 1).re :=
  fourFactor_rawLandauSiegelLowerBound (1/10000) (by norm_num)

end AnalyticNumberTheory.LargeSieve
