import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySievedReciprocalInterval
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainTerm

/-!
# One coprimality sieve on a unit residue-class interval

Finite Mobius inversion costs only the divisors of the specified sieve
integer. No coprimality between that integer and either modulus is assumed:
divisors meeting the phase modulus vanish intrinsically, and divisors meeting
the progression modulus are excluded by the unit residue. The surviving
divisor sections are CRT progressions of step `e * v`.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def sievedReciprocalInterval (q : ℕ) [NeZero q] (d : ℤ) (b v A L U : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc L U,
    if k % v = b % v ∧ k.Coprime A then reciprocalPhase q d k else 0

def reciprocalDivisorInterval (q : ℕ) [NeZero q] (d : ℤ) (b v e L U : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc L U,
    if k % v = b % v ∧ e ∣ k then reciprocalPhase q d k else 0

/-- A divisor sharing the phase modulus forces every term to be a nonunit. -/
theorem reciprocalDivisorInterval_eq_zero_of_not_coprime_modulus
    (q : ℕ) [NeZero q] (d : ℤ) (b v e L U : ℕ) (heq : ¬ e.Coprime q) :
    reciprocalDivisorInterval q d b v e L U = 0 := by
  unfold reciprocalDivisorInterval
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · have hku : ¬ IsUnit (k : ZMod q) := by
      intro hu
      exact heq (((ZMod.isUnit_iff_coprime k q).mp hu).of_dvd_left hk.2)
    simp only [reciprocalPhase, if_neg hku]
  · rfl

/-- A divisor sharing the step cannot divide an integer in a unit residue. -/
theorem reciprocalDivisorInterval_eq_zero_of_not_coprime_step
    (q : ℕ) [NeZero q] (d : ℤ) (b v e L U : ℕ)
    (hbv : b.Coprime v) (hev : ¬ e.Coprime v) :
    reciprocalDivisorInterval q d b v e L U = 0 := by
  unfold reciprocalDivisorInterval
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · have hkv : k.Coprime v := by
      change k.gcd v = 1
      exact (Nat.ModEq.gcd_eq hk.1).trans hbv
    exact False.elim (hev (hkv.of_dvd_left hk.2))
  · rfl

/-- CRT gives one residue class modulo `e*v`, not an arbitrary filtered AP. -/
theorem reciprocalDivisorInterval_eq_crt
    (q : ℕ) [NeZero q] (d : ℤ) (b v e L U : ℕ) (hev : e.Coprime v) :
    reciprocalDivisorInterval q d b v e L U =
      reciprocalResidueInterval q d (Nat.chineseRemainder hev 0 b) (e * v) L U := by
  unfold reciprocalDivisorInterval reciprocalResidueInterval
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply propext
  constructor
  · intro hk
    exact Nat.chineseRemainder_modEq_unique hev
      (Nat.modEq_zero_iff_dvd.mpr hk.2) hk.1
  · intro hk
    have he := (Nat.modEq_and_modEq_iff_modEq_mul hev).mpr hk
    constructor
    · exact he.2.trans (Nat.chineseRemainder hev 0 b).prop.2
    · exact Nat.modEq_zero_iff_dvd.mp
        (he.1.trans (Nat.chineseRemainder hev 0 b).prop.1)

/-- The finite Mobius expansion holds for the actual complex-valued phase. -/
theorem sievedReciprocalInterval_eq_moebius
    (q : ℕ) [NeZero q] (d : ℤ) (b v A L U : ℕ) (hA : A ≠ 0) :
    sievedReciprocalInterval q d b v A L U =
      ∑ e ∈ A.divisors, (ArithmeticFunction.moebius e : ℂ) *
        reciprocalDivisorInterval q d b v e L U := by
  have hind (k : ℕ) :
      (if k.Coprime A then (1 : ℂ) else 0) =
        ∑ e ∈ A.divisors, if e ∣ k then (ArithmeticFunction.moebius e : ℂ) else 0 := by
    have h := congrArg (fun x : ℝ ↦ (x : ℂ)) (coprime_indicator_eq_moebius hA k)
    simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_intCast] using h
  unfold sievedReciprocalInterval reciprocalDivisorInterval
  calc
    _ = ∑ k ∈ Finset.Icc L U,
        (∑ e ∈ A.divisors, if e ∣ k then (ArithmeticFunction.moebius e : ℂ) else 0) *
          (if k % v = b % v then reciprocalPhase q d k else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hind]
      split_ifs <;> simp_all
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp_all

/-- Divisors meeting either modulus can be deleted before estimating. -/
theorem sievedReciprocalInterval_eq_moebius_unit_divisors
    (q : ℕ) [NeZero q] (d : ℤ) (b v A L U : ℕ)
    (hA : A ≠ 0) (hbv : b.Coprime v) :
    sievedReciprocalInterval q d b v A L U =
      ∑ e ∈ A.divisors.filter (fun e ↦ e.Coprime q ∧ e.Coprime v),
        (ArithmeticFunction.moebius e : ℂ) * reciprocalDivisorInterval q d b v e L U := by
  rw [sievedReciprocalInterval_eq_moebius q d b v A L U hA, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases heq : e.Coprime q
  · by_cases hev : e.Coprime v
    · exact (if_pos ⟨heq, hev⟩).symm
    · rw [if_neg (by tauto),
        reciprocalDivisorInterval_eq_zero_of_not_coprime_step q d b v e L U hbv hev,
        mul_zero]
  · rw [if_neg (by tauto),
      reciprocalDivisorInterval_eq_zero_of_not_coprime_modulus q d b v e L U heq,
      mul_zero]

/-- Each surviving divisor keeps the stronger interval length divided by `e*v`. -/
theorem reciprocalDivisorInterval_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (b v e L U : ℕ),
      0 < v → v.Coprime q → 0 < e → e.Coprime q → e.Coprime v →
      ‖reciprocalDivisorInterval q d b v e L U‖ ≤
        C * (1 + ((U - L + 1 : ℕ) : ℝ) / ((e : ℝ) * v * q)) *
          Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalResidueInterval_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro q hq d b v e L U hv hvq he heq hev
  rw [reciprocalDivisorInterval_eq_crt q d b v e L U hev]
  simpa only [Nat.cast_mul] using hbound q hq d
    (Nat.chineseRemainder hev 0 b) (e * v) L U (Nat.mul_pos he hv) (heq.mul_left hvq)

/-- Cancellation on one genuine sieved residue interval.

The constant depends only on `ε`. In particular, `A` need not be coprime to
`q` or `v`. The divisor cost is only `A.divisors.card`; the original interval
span is divided by `v*q`, with no loss of the progression saving.
-/
theorem sievedReciprocalInterval_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (b v A L U : ℕ),
      0 < v → v.Coprime q → b.Coprime v → 0 < A →
      ‖sievedReciprocalInterval q d b v A L U‖ ≤
        C * (A.divisors.card : ℝ) *
          (1 + ((U - L + 1 : ℕ) : ℝ) / ((v : ℝ) * q)) *
          Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalDivisorInterval_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro q hq d b v A L U hv hvq hbv hA
  let B : ℝ := C * (1 + ((U - L + 1 : ℕ) : ℝ) / ((v : ℝ) * q)) *
    Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdiv (e : ℕ) (heA : e ∈ A.divisors) :
      ‖reciprocalDivisorInterval q d b v e L U‖ ≤ B := by
    by_cases heq : e.Coprime q
    · by_cases hev : e.Coprime v
      · have he : 0 < e := Nat.pos_of_mem_divisors heA
        have hb := hbound q hq d b v e L U hv hvq he heq hev
        have hqr : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
        have hvr : (0 : ℝ) < v := by exact_mod_cast hv
        have her : (1 : ℝ) ≤ e := by exact_mod_cast he
        have hden : (v : ℝ) * q ≤ (e : ℝ) * v * q := by
          simpa only [one_mul, mul_assoc] using
            mul_le_mul_of_nonneg_right her (mul_pos hvr hqr).le
        have hf := div_le_div_of_nonneg_left
          (show (0 : ℝ) ≤ (U - L + 1 : ℕ) by positivity) (mul_pos hvr hqr) hden
        apply hb.trans
        dsimp [B]
        gcongr
      · rw [reciprocalDivisorInterval_eq_zero_of_not_coprime_step q d b v e L U hbv hev,
          norm_zero]
        exact hB
    · rw [reciprocalDivisorInterval_eq_zero_of_not_coprime_modulus q d b v e L U heq,
        norm_zero]
      exact hB
  rw [sievedReciprocalInterval_eq_moebius q d b v A L U hA.ne']
  calc
    _ ≤ ∑ e ∈ A.divisors,
        ‖(ArithmeticFunction.moebius e : ℂ) * reciprocalDivisorInterval q d b v e L U‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _e ∈ A.divisors, B := by
      apply Finset.sum_le_sum
      intro e heA
      rw [norm_mul]
      have hmu : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e))
      simpa only [one_mul] using mul_le_mul hmu (hdiv e heA) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; dsimp [B]; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
