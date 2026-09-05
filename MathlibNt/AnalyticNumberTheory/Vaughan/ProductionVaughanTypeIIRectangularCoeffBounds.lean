import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIRectangularSharpBridge
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
# Honest coefficient bounds for the Type-II rectangular bridge
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Finite Cauchy--Schwarz in the form needed for coefficient `L¹` masses. -/
theorem finite_norm_sum_sq_le_card_mul_energy
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) :
    (∑ x ∈ S, ‖a x‖) ^ 2 ≤
      (S.card : ℝ) * ∑ x ∈ S, Complex.normSq (a x) := by
  calc
    (∑ x ∈ S, ‖a x‖) ^ 2 ≤
        (∑ x ∈ S, ‖a x‖ ^ 2) * (∑ _x ∈ S, (1 : ℝ) ^ 2) := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S
        (fun x => ‖a x‖) (fun _ => (1 : ℝ))
    _ = (S.card : ℝ) * ∑ x ∈ S, Complex.normSq (a x) := by
      simp [Complex.normSq_eq_norm_sq, mul_comm]

/-- Cauchy--Schwarz connector for the rectangular coefficient `L¹` mass. -/
theorem rectangularCoefficientL1_sq_le_card_mul_energies
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb : ℕ) :
    rectangularCoefficientL1 a b Ma Mb Na Nb ^ 2 ≤
      ((Finset.Icc (Ma + 1) (Ma + Na)).card : ℝ) *
        (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), Complex.normSq (a m)) *
      (((Finset.Icc (Mb + 1) (Mb + Nb)).card : ℝ) *
        (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), Complex.normSq (b n))) := by
  unfold rectangularCoefficientL1
  rw [mul_pow]
  exact mul_le_mul
    (finite_norm_sum_sq_le_card_mul_energy _ a)
    (finite_norm_sum_sq_le_card_mul_energy _ b)
    (sq_nonneg _)
    (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _))

/-- The left rectangular coefficient has the literal dyadic-shell energy. -/
theorem vaughanTypeIIRectLeftCoeff_energy_le
    (N u k : ℕ) :
    (∑ d ∈ Finset.Icc ((2 ^ k : ℕ) : ℤ)
        (((2 ^ (k + 1) - 1 : ℕ) : ℤ)),
      Complex.normSq (vaughanTypeIIRectLeftCoeff N u k d)) ≤
      ((2 ^ k : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc ((2 ^ k : ℕ) : ℤ)
        (((2 ^ (k + 1) - 1 : ℕ) : ℤ)), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      unfold vaughanTypeIIRectLeftCoeff
      split_ifs with h
      · rw [Complex.normSq_eq_norm_sq]
        rcases ArithmeticFunction.moebius_eq_or d.toNat with hμ | hμ | hμ <;>
          simp [vaughanMoebiusCoeff, hμ]
      · simp
    _ = ((2 ^ k : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      norm_cast
      rw [Int.card_Icc]
      have hp : 1 ≤ 2 ^ (k + 1) := (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
      rw [Nat.cast_sub hp]
      have heq : (((2 ^ (k + 1) : ℕ) : ℤ) - (1 : ℕ) + 1 -
          ((2 ^ k : ℕ) : ℤ)) = ((2 ^ k : ℕ) : ℤ) := by
        push_cast
        rw [pow_succ]
        ring
      rw [heq, Int.toNat_natCast]

/-- Norm-square form of finite Cauchy--Schwarz. -/
theorem normSq_finset_sum_le_card_mul_energy
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) :
    Complex.normSq (∑ x ∈ S, a x) ≤
      (S.card : ℝ) * ∑ x ∈ S, Complex.normSq (a x) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ x ∈ S, a x‖ ^ 2 ≤ (∑ x ∈ S, ‖a x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S a) 2
    _ ≤ _ := finite_norm_sum_sq_le_card_mul_energy S a

private theorem vaughanTypeIIRectRightCoeff_normSq_le_divisor
    (N v l X : ℕ) (t : ℤ) (ht : t ∈ Finset.Icc (1 : ℤ) X) :
    Complex.normSq (vaughanTypeIIRectRightCoeff N v l t) ≤
      (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (X + 1 : ℕ) ^ 2 := by
  let S := (vaughanCanonicalDyadicBlock N v l).filter (fun e => e ∣ t.toNat)
  have htI := Finset.mem_Icc.mp ht
  have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one htI.1
  have htnatpos : 0 < t.toNat := by omega
  have htX : t.toNat ≤ X := by
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
    exact_mod_cast htcast.trans_le htI.2
  have hSsub : S ⊆ t.toNat.divisors := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Nat.mem_divisors.mpr ⟨he'.2, htnatpos.ne'⟩
  have hcard : (S.card : ℝ) ≤ (t.toNat.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSsub
  have hterm : ∀ e ∈ S,
      Complex.normSq (vaughanMangoldtCoeff e) ≤ Real.log (X + 1 : ℕ) ^ 2 := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have hepos : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he'.1).1
    have het : e ≤ t.toNat := Nat.le_of_dvd htnatpos he'.2
    have hlog : Real.log (e : ℝ) ≤ Real.log (X + 1 : ℕ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < e
        exact_mod_cast hepos
      · show (0 : ℝ) < (X + 1 : ℕ)
        positivity
      · exact_mod_cast (het.trans htX).trans (Nat.le_succ X)
    rw [Complex.normSq_eq_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    calc
      ‖vaughanMangoldtCoeff e‖ = ArithmeticFunction.vonMangoldt e := by
        simp [vaughanMangoldtCoeff,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ Real.log (e : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (X + 1 : ℕ) := hlog
  have henergy : (∑ e ∈ S, Complex.normSq (vaughanMangoldtCoeff e)) ≤
      (S.card : ℝ) * Real.log (X + 1 : ℕ) ^ 2 := by
    calc
      _ ≤ ∑ _e ∈ S, Real.log (X + 1 : ℕ) ^ 2 := Finset.sum_le_sum hterm
      _ = _ := by simp
  have hrewrite : vaughanTypeIIRectRightCoeff N v l t =
      ∑ e ∈ S, vaughanMangoldtCoeff e := by
    unfold vaughanTypeIIRectRightCoeff S
    rw [Finset.sum_filter]
  rw [hrewrite]
  calc
    Complex.normSq (∑ e ∈ S, vaughanMangoldtCoeff e) ≤
        (S.card : ℝ) * ∑ e ∈ S, Complex.normSq (vaughanMangoldtCoeff e) :=
      normSq_finset_sum_le_card_mul_energy S _
    _ ≤ (S.card : ℝ) * ((S.card : ℝ) * Real.log (X + 1 : ℕ) ^ 2) := by
      gcongr
    _ ≤ (t.toNat.divisors.card : ℝ) *
        ((t.toNat.divisors.card : ℝ) * Real.log (X + 1 : ℕ) ^ 2) := by
      gcongr
    _ = (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (X + 1 : ℕ) ^ 2 := by ring

/-- The right rectangular coefficient is paid by the honest divisor-square
moment on its displayed interval. -/
theorem vaughanTypeIIRectRightCoeff_energy_le
    (N v k l : ℕ) :
    (∑ t ∈ Finset.Icc ((2 ^ l : ℕ) : ℤ) ((N / 2 ^ k : ℕ) : ℤ),
      Complex.normSq (vaughanTypeIIRectRightCoeff N v l t)) ≤
      27 * ((N / 2 ^ k : ℕ) : ℝ) *
        Real.log (N / 2 ^ k + 1 : ℕ) ^ 5 := by
  let X := N / 2 ^ k
  have hsub : Finset.Icc ((2 ^ l : ℕ) : ℤ) (X : ℤ) ⊆
      Finset.Icc (1 : ℤ) (X : ℤ) := by
    intro t ht
    have hpow : 1 ≤ 2 ^ l :=
      (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
    exact Finset.mem_Icc.mpr ⟨
      (show (1 : ℤ) ≤ (2 ^ l : ℕ) by exact_mod_cast hpow).trans
        (Finset.mem_Icc.mp ht).1,
      (Finset.mem_Icc.mp ht).2⟩
  calc
    (∑ t ∈ Finset.Icc ((2 ^ l : ℕ) : ℤ) (X : ℤ),
        Complex.normSq (vaughanTypeIIRectRightCoeff N v l t)) ≤
      ∑ t ∈ Finset.Icc (1 : ℤ) (X : ℤ),
        Complex.normSq (vaughanTypeIIRectRightCoeff N v l t) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun t ht hnot => Complex.normSq_nonneg _)
    _ ≤ ∑ t ∈ Finset.Icc (1 : ℤ) (X : ℤ),
        (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (X + 1 : ℕ) ^ 2 := by
          exact Finset.sum_le_sum fun t ht =>
            vaughanTypeIIRectRightCoeff_normSq_le_divisor N v l X t ht
    _ = divisorSquarePrefix X * Real.log (X + 1 : ℕ) ^ 2 := by
          unfold divisorSquarePrefix
          rw [Finset.sum_mul]
    _ ≤ (27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 3) *
        Real.log (X + 1 : ℕ) ^ 2 := by
          gcongr
          exact divisorSquareMomentBound_27 X
    _ = 27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 5 := by ring
    _ = 27 * ((N / 2 ^ k : ℕ) : ℝ) *
        Real.log (N / 2 ^ k + 1 : ℕ) ^ 5 := by rfl

end
end AnalyticNumberTheory.LargeSieve
