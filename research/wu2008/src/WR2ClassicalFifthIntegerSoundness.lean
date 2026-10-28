import WR2ClassicalFifthIntegerDomains
import WR2ClassicalFifthTableCheck

/-! Exact payment identities and lower bounds on the original Fifth grids.
High-degree logarithm expressions remain abstract in the payment algebra. -/
namespace WuPaper.FifthIntegerPayment
open IntegerLogHorner

private theorem denominator_pos {q : ℕ} (hq : 0 < q) : 0 < denominator q := by
  unfold denominator IntegerLogHorner.commonDen
  positivity

def sample (b : Branch) (i : ℕ) : ℚ :=
  (gridNumerator b i : ℚ) / (gridDenominator b : ℚ)

theorem first_log (b : Branch) {i : ℕ} (hi : i < 1024) :
    (numerator (gridNumerator b i-2*gridDenominator b) (gridNumerator b i):ℚ) /
      (denominator (gridNumerator b i):ℚ) = ExactRational.logLo (sample b i-1) := by
  obtain ⟨hd,hs,_⟩ := grid_domain b hi
  have hds : gridDenominator b ≤ gridNumerator b i := by omega
  have hnd : gridDenominator b ≤ gridNumerator b i-gridDenominator b := by omega
  have he := logLo_nat_ratio hnd hd
  have hsub : gridNumerator b i-gridDenominator b-gridDenominator b =
      gridNumerator b i-2*gridDenominator b := by omega
  have hadd : gridNumerator b i-gridDenominator b+gridDenominator b =
      gridNumerator b i := by omega
  rw [hsub,hadd] at he
  rw [← he, Nat.cast_sub hds]
  congr 1
  unfold sample
  have hdq : (gridDenominator b:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdq]

theorem second_log (b : Branch) {i : ℕ} (hi : i < 1024) :
    (numerator (ratioNumerator b i-ratioDenominator b i)
      (ratioNumerator b i+ratioDenominator b i):ℚ) /
      (denominator (ratioNumerator b i+ratioDenominator b i):ℚ) =
    ExactRational.logLo ((ratioNumerator b i:ℚ)/(ratioDenominator b i:ℚ)) := by
  obtain ⟨hd,hn⟩ := ratio_domain b hi
  exact (logLo_nat_ratio hn hd).symm

private theorem extra_exact (b : Branch) (hb : b ≠ .initial)
    {i : ℕ} (hi : i < 1024) :
    (extraNumerator b i:ℚ)/(extraDenominator b:ℚ) =
      ClassicalFifthTableCheck.cPoly (sample b i-4) := by
  obtain ⟨hsub,hy⟩ := extra_domain b hb hi
  have hd := (grid_domain b hi).1
  have hp := FifthIntegerPolynomial.cPoly_nat hy hd
  have hx : ((gridNumerator b i-4*gridDenominator b:ℕ):ℚ)/(gridDenominator b:ℚ)
      = sample b i-4 := by
    rw [Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_ofNat]
    unfold sample
    have hdq : (gridDenominator b:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  rw [hx] at hp
  cases b with
  | initial => exact (hb rfl).elim
  | middle => simpa only [extraNumerator, extraDenominator, Nat.cast_mul, Nat.cast_pow] using hp
  | terminal => simpa only [extraNumerator, extraDenominator, Nat.cast_mul, Nat.cast_pow] using hp

/-- This low-degree identity never sees the polynomial or log implementation. -/
private theorem weight_identity (S D : ℚ) (hd : D ≠ 0) :
    (S/D)*(1/2-(100/1327)*(S/D)) = S*(1327*D-200*S)/(2654*D^2) := by
  field_simp [hd]
  ring

private theorem payment_algebra (K D S A B C E F G : ℚ)
    (hd : D ≠ 0) (hs : S ≠ 0) (hb : B ≠ 0) (he : E ≠ 0)
    (hg : G ≠ 0) (_hw : 1327*D-200*S ≠ 0) :
    K*2654*D^2*(A*E+C*B)*F/(B*E*G*S*(1327*D-200*S)) =
    K*((A/B+C/E)*(F/G)/((S/D)*(1/2-(100/1327)*(S/D)))) := by
  rw [weight_identity S D hd]
  field_simp [hd, hs, hb, he, hg, _hw]

private theorem raw_exact (b : Branch) {i : ℕ} (hi : i < 1024) :
    (rawNumerator b i:ℚ)/(rawDenominator b i:ℚ) =
    (scale:ℚ)*ClassicalFifthTableCheck.value
      ((extraNumerator b i:ℚ)/(extraDenominator b:ℚ))
      ((ratioNumerator b i:ℚ)/(ratioDenominator b i:ℚ)) (sample b i) := by
  obtain ⟨hd,hs,hw⟩ := grid_domain b hi
  obtain ⟨hr,hn⟩ := ratio_domain b hi
  have hsp : 0 < gridNumerator b i := by omega
  have hep : 0 < extraDenominator b := by
    cases b <;> norm_num [extraDenominator, FifthIntegerPolynomial.commonDen, gridDenominator]
  have hbp := denominator_pos hsp
  have hgp : 0 < denominator (ratioNumerator b i+ratioDenominator b i) :=
    denominator_pos (by omega)
  have hdq : (gridDenominator b:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsq : (gridNumerator b i:ℚ) ≠ 0 := by exact_mod_cast hsp.ne'
  have heq : (extraDenominator b:ℚ) ≠ 0 := by exact_mod_cast hep.ne'
  have hbq : (denominator (gridNumerator b i):ℚ) ≠ 0 := by exact_mod_cast hbp.ne'
  have hgq : (denominator (ratioNumerator b i+ratioDenominator b i):ℚ) ≠ 0 := by
    exact_mod_cast hgp.ne'
  have hwq : (1327:ℚ)*(gridDenominator b:ℚ)-200*(gridNumerator b i:ℚ) ≠ 0 := by
    have h : (200:ℚ)*(gridNumerator b i:ℚ) < 1327*(gridDenominator b:ℚ) := by exact_mod_cast hw
    linarith
  simp only [rawNumerator, rawDenominator, Nat.cast_mul, Nat.cast_add,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub (Nat.le_of_lt hw)]
  rw [payment_algebra _ _ _ _ _ _ _ _ _ hdq hsq hbq heq hgq hwq]
  rw [first_log b hi, second_log b hi]
  rfl

-- BRANCH BRIDGES

theorem initial_midpoint (i : ℕ) : sample .initial i =
    ExactRational.midpoint ClassicalFifthTableCheck.lo 4 1024 i := by
  simp only [sample, gridNumerator, gridDenominator, ExactRational.midpoint,
    ClassicalFifthTableCheck.lo,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem initial_ratio {i : ℕ} (hi : i < 1024) :
    (ratioNumerator .initial i:ℚ)/(ratioDenominator .initial i:ℚ) = (1327/824)/(1327/200-1327/824-sample .initial i) := by
  have h := initial_ratio_domain hi
  have hq : (164800:ℚ)*(gridNumerator .initial i:ℚ) <
      828048*(gridDenominator .initial:ℚ) := by exact_mod_cast h.1
  have hdiv : (1327/200:ℚ)-1327/824-sample .initial i ≠ 0 := by
    simp only [sample, gridDenominator] at *
    norm_num only [Nat.cast_ofNat] at hq ⊢
    intro hz
    linarith
  have hden : (828048:ℚ)*(gridDenominator .initial:ℚ)-
      164800*(gridNumerator .initial i:ℚ) ≠ 0 := by linarith
  simp only [ratioNumerator, ratioDenominator]
  rw [Nat.cast_sub (Nat.le_of_lt h.1)]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  unfold sample at hdiv ⊢
  norm_num only [gridDenominator, Nat.cast_ofNat] at hdiv hden ⊢
  apply (div_eq_div_iff hden hdiv).2
  ring

theorem initial_raw_exact {i : ℕ} (hi : i < 1024) :
    (rawNumerator .initial i:ℚ)/(rawDenominator .initial i:ℚ) =
      (scale:ℚ)*ClassicalFifthTableCheck.initialValue (sample .initial i) := by
  have h := raw_exact .initial hi
  rw [initial_ratio hi] at h
  simp only [extraNumerator, extraDenominator, Nat.cast_zero, Nat.cast_one, zero_div] at h
  exact h

theorem initial_payment_condition {i : ℕ} (hi : i < 1024) :
    ClassicalFifthTableCheck.initialCondition (paymentNumerator .initial) i := by
  have h := quotient_payment_of_exact (by norm_num [scale] : 0 < scale)
    (initial_raw_exact hi)
  simpa only [ClassicalFifthTableCheck.initialCondition, paymentNumerator, if_pos hi,
    scale, Nat.cast_ofNat, initial_midpoint] using h

theorem initial_payment_sound {i : ℕ} (hi : i < 1024) :
    (paymentNumerator .initial i:ℝ)/1000000000000 ≤
      ClassicalFifthRational.initialValue
        ((ClassicalUniformMidpoint.point ClassicalFifthSource.lo 4 1024 i +
          ClassicalUniformMidpoint.point ClassicalFifthSource.lo 4 1024 (i+1))/2) := by
  exact ClassicalFifthTableCheck.initialCondition_sound (initial_payment_condition hi)

theorem middle_midpoint (i : ℕ) : sample .middle i =
    ExactRational.midpoint 4 ClassicalFifthTableCheck.cut 1024 i := by
  simp only [sample, gridNumerator, gridDenominator, ExactRational.midpoint,
    ClassicalFifthTableCheck.cut,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem middle_ratio {i : ℕ} (hi : i < 1024) :
    (ratioNumerator .middle i:ℚ)/(ratioDenominator .middle i:ℚ) = (1327/824)/(1327/200-1327/824-sample .middle i) := by
  have h := middle_ratio_domain hi
  have hq : (164800:ℚ)*(gridNumerator .middle i:ℚ) <
      828048*(gridDenominator .middle:ℚ) := by exact_mod_cast h.1
  have hdiv : (1327/200:ℚ)-1327/824-sample .middle i ≠ 0 := by
    simp only [sample, gridDenominator] at *
    norm_num only [Nat.cast_ofNat] at hq ⊢
    intro hz
    linarith
  have hden : (828048:ℚ)*(gridDenominator .middle:ℚ)-
      164800*(gridNumerator .middle i:ℚ) ≠ 0 := by linarith
  simp only [ratioNumerator, ratioDenominator]
  rw [Nat.cast_sub (Nat.le_of_lt h.1)]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  unfold sample at hdiv ⊢
  norm_num only [gridDenominator, Nat.cast_ofNat] at hdiv hden ⊢
  apply (div_eq_div_iff hden hdiv).2
  ring

theorem middle_raw_exact {i : ℕ} (hi : i < 1024) :
    (rawNumerator .middle i:ℚ)/(rawDenominator .middle i:ℚ) =
      (scale:ℚ)*ClassicalFifthTableCheck.middleValue (sample .middle i) := by
  have h := raw_exact .middle hi
  rw [middle_ratio hi] at h
  rw [extra_exact .middle (by decide) hi] at h
  exact h

theorem middle_payment_condition {i : ℕ} (hi : i < 1024) :
    ClassicalFifthTableCheck.middleCondition (paymentNumerator .middle) i := by
  have h := quotient_payment_of_exact (by norm_num [scale] : 0 < scale)
    (middle_raw_exact hi)
  simpa only [ClassicalFifthTableCheck.middleCondition, paymentNumerator, if_pos hi,
    scale, Nat.cast_ofNat, middle_midpoint] using h

theorem middle_payment_sound {i : ℕ} (hi : i < 1024) :
    (paymentNumerator .middle i:ℝ)/1000000000000 ≤
      ClassicalFifthRational.middleValue
        ((ClassicalUniformMidpoint.point 4 ClassicalFifthSource.cut 1024 i +
          ClassicalUniformMidpoint.point 4 ClassicalFifthSource.cut 1024 (i+1))/2) := by
  exact ClassicalFifthTableCheck.middleCondition_sound (middle_payment_condition hi)

theorem terminal_midpoint (i : ℕ) : sample .terminal i =
    ExactRational.midpoint ClassicalFifthTableCheck.cut ClassicalFifthTableCheck.hi 1024 i := by
  simp only [sample, gridNumerator, gridDenominator, ExactRational.midpoint,
    ClassicalFifthTableCheck.cut, ClassicalFifthTableCheck.hi,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem terminal_ratio {i : ℕ} (hi : i < 1024) :
    (ratioNumerator .terminal i:ℚ)/(ratioDenominator .terminal i:ℚ) = 1327/200-1-sample .terminal i := by
  have h := terminal_ratio_domain hi
  simp only [ratioNumerator, ratioDenominator]
  rw [Nat.cast_sub h.1]
  simp only [Nat.cast_mul, Nat.cast_ofNat, sample, gridDenominator]
  field_simp
  ring

theorem terminal_raw_exact {i : ℕ} (hi : i < 1024) :
    (rawNumerator .terminal i:ℚ)/(rawDenominator .terminal i:ℚ) =
      (scale:ℚ)*ClassicalFifthTableCheck.terminalValue (sample .terminal i) := by
  have h := raw_exact .terminal hi
  rw [terminal_ratio hi] at h
  rw [extra_exact .terminal (by decide) hi] at h
  exact h

theorem terminal_payment_condition {i : ℕ} (hi : i < 1024) :
    ClassicalFifthTableCheck.terminalCondition (paymentNumerator .terminal) i := by
  have h := quotient_payment_of_exact (by norm_num [scale] : 0 < scale)
    (terminal_raw_exact hi)
  simpa only [ClassicalFifthTableCheck.terminalCondition, paymentNumerator, if_pos hi,
    scale, Nat.cast_ofNat, terminal_midpoint] using h

theorem terminal_payment_sound {i : ℕ} (hi : i < 1024) :
    (paymentNumerator .terminal i:ℝ)/1000000000000 ≤
      ClassicalFifthRational.terminalValue
        ((ClassicalUniformMidpoint.point ClassicalFifthSource.cut ClassicalFifthSource.hi 1024 i +
          ClassicalUniformMidpoint.point ClassicalFifthSource.cut ClassicalFifthSource.hi 1024 (i+1))/2) := by
  exact ClassicalFifthTableCheck.terminalCondition_sound (terminal_payment_condition hi)

end WuPaper.FifthIntegerPayment
#print axioms WuPaper.FifthIntegerPayment.initial_payment_sound
#print axioms WuPaper.FifthIntegerPayment.middle_payment_sound
#print axioms WuPaper.FifthIntegerPayment.terminal_payment_sound
