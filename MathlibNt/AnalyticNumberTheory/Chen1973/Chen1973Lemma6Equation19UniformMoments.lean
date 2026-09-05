/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19MomentTransport

/-!
# Chen 1973, Lemma 6, equation (19): uniform moment constants

This leaf freezes the sharp Lemma-2 constant before every coefficient, spectral
height, and cell parameter.  It also records injectivity of the actual ordered
prime-pair shell, the structural input needed to pay its collected coefficient
energy without a collision multiplicity.  No final-cell estimate is assumed.
-/

noncomputable section

set_option maxHeartbeats 800000

open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The real sharp Lemma-2 package, with its absolute constant selected once. -/
private theorem eq19SharpRealPackage : Chen1973Lemma2EquationThree :=
  chen1973Lemma2_equationThree_of_equationTwo
    (chen1973Lemma2_equationTwo_of_fareyEquationFour chen1973FareyEquationFour)

/-- One fixed global constant for all complex-coefficient uses of sharp Lemma 2. -/
def chen1973Lemma6Eq19SharpConstant : ℝ :=
  2 * Classical.choose eq19SharpRealPackage

lemma chen1973Lemma6_eq19SharpConstant_pos :
    0 < chen1973Lemma6Eq19SharpConstant := by
  unfold chen1973Lemma6Eq19SharpConstant
  exact mul_pos (by norm_num) (Classical.choose_spec eq19SharpRealPackage).1

/-- Complex sharp Lemma 2 with a single constant chosen before the coefficient
sequence and all interval/conductor parameters. -/
theorem chen1973Lemma2_equationThree_complex_fixed
    (c : ℤ → ℂ) (M : ℤ) (N D Q : ℕ) (hD : 0 < D) :
    (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      chen1973Lemma6Eq19SharpConstant *
        ((Q : ℝ) + (N : ℝ) / D) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
  let C : ℝ := Classical.choose eq19SharpRealPackage
  change _ ≤ 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
    ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2
  have hC := (Classical.choose_spec eq19SharpRealPackage).2
  let aR : ℤ → ℝ := fun n => (c n).re
  let aI : ℤ → ℝ := fun n => (c n).im
  have hp (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2 ≤
        2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
          ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
    let AR := chen1973PrimitiveAmplitude aR M N q χ
    let AI := chen1973PrimitiveAmplitude aI M N q χ
    have heq : (∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)) =
        AR + I * AI := by
      dsimp [AR, AI, chen1973PrimitiveAmplitude]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      calc
        c n * χ.1 (n : ZMod q) =
            (((c n).re : ℂ) + ((c n).im : ℂ) * I) * χ.1 (n : ZMod q) := by
              rw [Complex.re_add_im]
        _ = ((c n).re : ℂ) * χ.1 (n : ZMod q) +
            I * (((c n).im : ℂ) * χ.1 (n : ZMod q)) := by ring
    rw [heq]
    have h := norm_add_le AR (I * AI)
    have hI : ‖I * AI‖ = ‖AI‖ := by simp
    rw [hI] at h
    have hsquare : ‖AR + I * AI‖ ^ 2 ≤ (‖AR‖ + ‖AI‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp [AR, AI]
    nlinarith [sq_nonneg (‖AR‖ - ‖AI‖)]
  have hR := hC aR M N D Q hD
  have hI := hC aI M N D Q hD
  calc
    _ ≤ ∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
            ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ hχ => hp q χ) (by positivity)
    _ = 2 * ((∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2) +
        (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aR M N +
        C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aI M N) := by
      gcongr
    _ = 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
      unfold chen1973CoefficientEnergy
      rw [show 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
          (∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) =
        2 * (C * ((Q : ℝ) + (N : ℝ) / D) *
          ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) by ring]
      apply congrArg (fun z : ℝ => 2 * z)
      rw [← mul_add, ← Finset.sum_add_distrib]
      apply congrArg (fun z : ℝ => C * ((Q : ℝ) + (N : ℝ) / D) * z)
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, sq_abs]
      ring

private lemma eq19_pair_shell_data
    {x B k m : ℕ} {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6PrimePairShell x B k m) :
    pp.1.Prime ∧ pp.2.Prime ∧ pp.1 < pp.2 := by
  simp only [chen1973Lemma6PrimePairShell, chen1973Lemma6DyadicShell,
    Finset.mem_filter] at hpp
  have hp := hpp.1.1
  rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hp
  refine ⟨hp.2.1, hp.2.2.1, ?_⟩
  have hle := hp.2.2.2.2.1
  have hlt := hp.2.2.2.2.2.1
  exact_mod_cast lt_of_le_of_lt hle hlt

/-- Products are injective on Chen's actual ordered prime-pair shell.  The
small/large prime separation rules out the swapped factorization. -/
theorem chen1973Lemma6_eq19_pair_product_injective
    (x B k m : ℕ) :
    Set.InjOn (fun pp : ℕ × ℕ => pp.1 * pp.2)
      (chen1973Lemma6PrimePairShell x B k m : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  obtain ⟨ha1, ha2, halt⟩ := eq19_pair_shell_data ha
  obtain ⟨hb1, hb2, hblt⟩ := eq19_pair_shell_data hb
  change a.1 * a.2 = b.1 * b.2 at hab
  have hdvd : a.1 ∣ b.1 * b.2 := ⟨a.2, hab.symm⟩
  rcases ha1.dvd_mul.mp hdvd with h11 | h12
  · have hac : a.1 = b.1 := by
      rcases (Nat.dvd_prime hb1).mp h11 with h | h
      · exact (ha1.ne_one h).elim
      · exact h
    have hsecond : a.2 = b.2 := by
      rw [hac] at hab
      exact Nat.eq_of_mul_eq_mul_left hb1.pos hab
    exact Prod.ext hac hsecond
  · have had : a.1 = b.2 := by
      rcases (Nat.dvd_prime hb2).mp h12 with h | h
      · exact (ha1.ne_one h).elim
      · exact h
    have hsecond : a.2 = b.1 := by
      rw [had] at hab
      apply Nat.eq_of_mul_eq_mul_right hb2.pos
      simpa [mul_comm] using hab
    omega

private lemma norm_collected_sq_eq_fiber_energy
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (a : ι → ℂ)
    (hg : Set.InjOn g (S : Set ι)) (y : κ) :
    ‖∑ i ∈ S, if g i = y then a i else 0‖ ^ 2 =
      ∑ i ∈ S with g i = y, ‖a i‖ ^ 2 := by
  let T := S.filter fun i => g i = y
  have hcard : T.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro i j hi hj
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    exact hg hi'.1 hj'.1 (hi'.2.trans hj'.2.symm)
  rw [← Finset.sum_filter]
  change ‖∑ i ∈ T, a i‖ ^ 2 = ∑ i ∈ T, ‖a i‖ ^ 2
  by_cases hT : T = ∅
  · rw [hT]
    simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hsingle : T = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hi, ?_⟩
      intro j hj
      exact (Finset.card_le_one.mp hcard) j hj i hi
    rw [hsingle]
    simp

/-- One atom in the literal ordered prime-pair coefficient energy. -/
def chen1973Lemma6Eq19PairAtom (x : ℕ) (s : ℂ) (pp : ℕ × ℕ) : ℂ :=
  1 / ((pp.1 * pp.2 : ℂ) ^ s *
    Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))

/-- The collected coefficient has exactly the energy of the actual ordered
dyadic pair shell.  In particular, no pair-collision multiplicity is lost. -/
theorem chen1973Lemma6_eq19_pairCoefficient_square_energy
    (x B k m : ℕ) (s : ℂ) :
    (∑ n ∈ Icc (1 : ℤ) (x * x : ℕ),
      ‖chen1973Lemma6Eq19PairCoefficient x B k m s n‖ ^ 2) =
      ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6Eq19PairAtom x s pp‖ ^ 2 := by
  let S := chen1973Lemma6PrimePairShell x B k m
  let g : ℕ × ℕ → ℤ := fun pp => pp.1 * pp.2
  have hg : Set.InjOn g (S : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact chen1973Lemma6_eq19_pair_product_injective x B k m ha hb
      (by
        change (a.1 * a.2 : ℤ) = b.1 * b.2 at hab
        exact_mod_cast hab)
  have hmap : ∀ pp ∈ S, g pp ∈ Finset.Icc (1 : ℤ) (x * x : ℕ) := by
    intro pp hpp
    change pp ∈ chen1973Lemma6PrimePairShell x B k m at hpp
    simp only [chen1973Lemma6PrimePairShell, chen1973Lemma6DyadicShell,
      Finset.mem_filter] at hpp
    have hp := hpp.1.1
    rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hp
    have hpRange := Finset.mem_product.mp hp.1
    have hp1 := Finset.mem_range.mp hpRange.1
    have hp2 := Finset.mem_range.mp hpRange.2
    rw [Finset.mem_Icc]
    constructor
    · change (1 : ℤ) ≤ ((pp.1 * pp.2 : ℕ) : ℤ)
      exact_mod_cast Nat.mul_pos hp.2.1.pos hp.2.2.1.pos
    · change ((pp.1 * pp.2 : ℕ) : ℤ) ≤ ((x * x : ℕ) : ℤ)
      exact_mod_cast Nat.mul_le_mul (Nat.le_of_lt_succ hp1) (Nat.le_of_lt_succ hp2)
  unfold chen1973Lemma6Eq19PairCoefficient
  change (∑ n ∈ Icc (1 : ℤ) (x * x : ℕ),
      ‖∑ pp ∈ S, if g pp = n then chen1973Lemma6Eq19PairAtom x s pp else 0‖ ^ 2) = _
  simp_rw [norm_collected_sq_eq_fiber_energy S g (chen1973Lemma6Eq19PairAtom x s) hg]
  rw [Finset.sum_fiberwise_of_maps_to hmap]

/-- Equation (15) with the global sharp constant; the constant is selected
before `H,D,Q,s` and hence before every vertical height. -/
theorem chen1973Lemma6_equation15_fixed_log_power
    (H D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d,
        ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4) ≤
      chen1973Lemma6Eq19SharpConstant *
        ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
        (1 + Real.log (H * H : ℕ)) ^ 4 := by
  have hLS := chen1973Lemma2_equationThree_complex_fixed
    (chen1973Lemma6MobiusSquareCoefficient H s) 0 (H * H) D Q hD
  have hident :
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4) =
      ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖∑ z ∈ Icc (1 : ℤ) (H * H : ℕ),
            chen1973Lemma6MobiusSquareCoefficient H s z *
              χ.1 (z : ZMod d)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [← chen1973Lemma6_mobiusPolynomial_sq_eq_collected, norm_pow]
    ring
  rw [hident]
  have hE :
      (∑ z ∈ Icc ((0 : ℤ) + 1) ((0 : ℤ) + (H * H : ℕ)),
        ‖chen1973Lemma6MobiusSquareCoefficient H s z‖ ^ 2) ≤
      (1 + Real.log (H * H : ℕ)) ^ 4 := by
    simpa only [Int.zero_add] using
      chen1973Lemma6_mobiusSquareCoefficient_energy_le_log_four H s hs
  have hLS' :
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖∑ z ∈ Icc (1 : ℤ) (H * H : ℕ),
            chen1973Lemma6MobiusSquareCoefficient H s z *
              χ.1 (z : ZMod d)‖ ^ 2) ≤
        chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          ∑ z ∈ Icc (1 : ℤ) (H * H : ℕ),
            ‖chen1973Lemma6MobiusSquareCoefficient H s z‖ ^ 2 := by
    simpa only [Int.zero_add] using hLS
  have hE' :
      (∑ z ∈ Icc (1 : ℤ) (H * H : ℕ),
        ‖chen1973Lemma6MobiusSquareCoefficient H s z‖ ^ 2) ≤
        (1 + Real.log (H * H : ℕ)) ^ 4 := by
    simpa only [Int.zero_add] using hE
  exact hLS'.trans (mul_le_mul_of_nonneg_left hE'
    (mul_nonneg (chen1973Lemma6_eq19SharpConstant_pos.le) (by positivity)))

/-- The literal pair-polynomial second moment, with the global sharp constant
and the exact ordered-pair coefficient energy.  Neither the constant nor the
coefficient support depends on a conductor cell. -/
theorem chen1973Lemma6_eq19_pair_second_moment_fixed
    (x L level B k m D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq19PairSecondMoment x L level B k m s ≤
      chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((x * x : ℕ) : ℝ) / D) *
          ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
            ‖chen1973Lemma6Eq19PairAtom x s pp‖ ^ 2) := by
  have hLS := chen1973Lemma2_equationThree_complex_fixed
    (chen1973Lemma6Eq19PairCoefficient x B k m s) 0 (x * x) D Q hD
  have hnon : ∀ d : ℕ, 0 ≤
      ∑ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
            ((pp.1 * pp.2 : ℂ) ^ s *
              Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ ^ 2 :=
    fun d => Finset.sum_nonneg fun χ hχ => sq_nonneg _
  unfold chen1973Lemma6Eq19PairSecondMoment
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
      chen1973Lemma6Eq19Weight d * _) ≤ _
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter d,
              ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
                χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
                  ((pp.1 * pp.2 : ℂ) ^ s *
                    Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ ^ 2 :=
      chen1973Lemma6_eq19_weight_transport _ hnon
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
              χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
                ((pp.1 * pp.2 : ℂ) ^ s *
                  Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hcell
        intro d hd hdnot
        positivity
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ = chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            ‖∑ n ∈ Icc (1 : ℤ) (x * x : ℕ),
              chen1973Lemma6Eq19PairCoefficient x B k m s n *
                χ.1 (n : ZMod d)‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [← chen1973Lemma6_eq19_pairPolynomial_eq_collected]
    _ ≤ chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((x * x : ℕ) : ℝ) / D) *
          ∑ n ∈ Icc (1 : ℤ) (x * x : ℕ),
            ‖chen1973Lemma6Eq19PairCoefficient x B k m s n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [Int.zero_add] using hLS)
        (chen1973Lemma6Eq19I_pos x L level).le
    _ = _ := by rw [chen1973Lemma6_eq19_pairCoefficient_square_energy]

/-- Equation (14), with the same global sharp constant as equations (15) and
Lemma 2.  The constant is fixed before `s` and hence before a vertical height. -/
theorem chen1973Lemma6_equation14_fixed_log_power
    (H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D) (hDQ : D < Q)
    (hs : 1 ≤ s.re) :
    (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2) ≤
      2 * chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (1 + Real.log (H * H : ℕ)) ^ 4 +
        2 * (Q : ℝ) *
          ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
            (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
              (1 + Real.log H)) ^ 2 := by
  let F : (d : ℕ) → PrimitiveCharacter d → ℂ := fun d χ =>
    ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      chen1973Lemma6CHWeightedCoefficient H s m * χ.1 (m : ZMod d)
  let R : (d : ℕ) → PrimitiveCharacter d → ℂ := fun d χ =>
    (chen1973PrimitiveLValue d s χ -
      chen1973Lemma6NaturalLPolynomial H s χ) *
        chen1973Lemma6NaturalMobiusPolynomial H s χ
  have hp (d : ℕ) (χ : PrimitiveCharacter d) :
      ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2 ≤
        2 * ‖F d χ‖ ^ 2 + 2 * ‖R d χ‖ ^ 2 := by
    rw [chen1973Lemma6_oneSubLS_eq_CH_sub_remainder hH]
    change ‖F d χ - R d χ‖ ^ 2 ≤ _
    have hn := norm_sub_le (F d χ) (R d χ)
    have hsquare : ‖F d χ - R d χ‖ ^ 2 ≤
        (‖F d χ‖ + ‖R d χ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖F d χ‖ - ‖R d χ‖)]
  have hfinite := chen1973Lemma2_equationThree_complex_fixed
    (chen1973Lemma6CHWeightedCoefficient H s) 0 (H * H) D Q hD
  have hE := chen1973Lemma6_CHWeightedCoefficient_energy_le_log_four H hH s hs
  have hR := chen1973Lemma6_equation14_remainderMoment_final_scalar
    H D Q s hH hD hDQ hs
  calc
    _ ≤ ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          (2 * ‖F d χ‖ ^ 2 + 2 * ‖R d χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ hχ => hp d χ) (by positivity)
    _ = 2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖F d χ‖ ^ 2) +
        2 * chen1973Lemma6Equation14RemainderMoment H D Q s := by
      change _ = 2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖F d χ‖ ^ 2) +
        2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖R d χ‖ ^ 2)
      simp_rw [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
            ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2) +
        2 * chen1973Lemma6Equation14RemainderMoment H D Q s := by
      apply add_le_add
      · have hf :
            (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
              ∑ χ : PrimitiveCharacter d, ‖F d χ‖ ^ 2) ≤
              chen1973Lemma6Eq19SharpConstant *
                ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
                ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
                  ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2 := by
            simpa only [Int.zero_add, F] using hfinite
        exact mul_le_mul_of_nonneg_left hf (by norm_num)
      · exact le_rfl
    _ ≤ _ := by
      have hfac : 0 ≤ 2 * chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num) chen1973Lemma6_eq19SharpConstant_pos.le)
          (add_nonneg (by positivity) (by positivity))
      calc
        _ ≤ 2 * chen1973Lemma6Eq19SharpConstant *
              ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
              (1 + Real.log (H * H : ℕ)) ^ 4 +
            2 * ((Q : ℝ) *
              ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
                (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
                  (1 + Real.log H)) ^ 2) := by
            exact add_le_add (by
              simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hE hfac)
              (mul_le_mul_of_nonneg_left hR (by norm_num))
        _ = _ := by ring

/-- Equation (14) transported to an equation-(19) cell, with its constant fixed
globally before the spectral parameter. -/
theorem chen1973Lemma6_eq19_oneSub_second_moment_fixed
    (x L level H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D)
    (hDQ : D < Q) (hs : 1 ≤ s.re)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq19OneSubSecondMoment x L level H s ≤
      chen1973Lemma6Eq19I x L level *
        (2 * chen1973Lemma6Eq19SharpConstant *
            ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
            (1 + Real.log (H * H : ℕ)) ^ 4 +
          2 * (Q : ℝ) *
            ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
              (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
                (1 + Real.log H)) ^ 2) := by
  unfold chen1973Lemma6Eq19OneSubSecondMoment
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
      chen1973Lemma6Eq19Weight d *
        ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2) ≤ _
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2 := by
      apply chen1973Lemma6_eq19_weight_transport
      intro d
      positivity
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hcell
        intro d hd hdnot
        positivity
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (chen1973Lemma6_equation14_fixed_log_power H D Q s hH hD hDQ hs)
      (chen1973Lemma6Eq19I_pos x L level).le

/-- `v`-uniform equation-(15) moment on an explicit closed height interval. -/
theorem chen1973Lemma6_eq19_mobius_fourth_moment_uniform
    (x L level H D Q : ℕ) (σ T : ℝ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q)
    (hdom : ∀ v ∈ Set.Icc (-T) T,
      Chen1973Lemma3Domain (σ + v * I) σ v) :
    ∀ v ∈ Set.Icc (-T) T,
      chen1973Lemma6Eq19MobiusFourthMoment x L level H (σ + v * I) ≤
        chen1973Lemma6Eq19I x L level *
          (chen1973Lemma6Eq19SharpConstant *
            ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
            (1 + Real.log (H * H : ℕ)) ^ 4) := by
  intro v hv
  unfold chen1973Lemma6Eq19MobiusFourthMoment
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
      chen1973Lemma6Eq19Weight d *
        ∑ χ : PrimitiveCharacter d,
          ‖chen1973Lemma6NaturalMobiusPolynomial H (σ + v * I) χ‖ ^ 4) ≤ _
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter d,
              ‖chen1973Lemma6NaturalMobiusPolynomial H (σ + v * I) χ‖ ^ 4 := by
      apply chen1973Lemma6_eq19_weight_transport
      intro d
      positivity
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            ‖chen1973Lemma6NaturalMobiusPolynomial H (σ + v * I) χ‖ ^ 4 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hcell
        intro d hd hdnot
        positivity
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (chen1973Lemma6_equation15_fixed_log_power H D Q (σ + v * I) hD
        (by simpa using hdom v hv))
      (chen1973Lemma6Eq19I_pos x L level).le

/-- A scalar equation-(14) envelope independent of the vertical parameter. -/
def chen1973Lemma6Eq19OneSubUniformEnvelope
    (H Q : ℕ) (σ T : ℝ) : ℝ :=
  ((40 * (|σ| + T) * Real.sqrt Q * Real.log Q *
    (((H + 1 : ℕ) : ℝ) ^ (-σ))) * (1 + Real.log H)) ^ 2

/-- The equation-(14) moment uniformly on a closed vertical interval.  The
sharp large-sieve constant and the complete scalar envelope are selected before
`v`, so this theorem can be placed under a height integral without choice. -/
theorem chen1973Lemma6_eq19_oneSub_second_moment_uniform
    (x L level H D Q : ℕ) (σ T : ℝ) (hH : 0 < H) (hD : 0 < D)
    (hDQ : D < Q) (hσ : 1 ≤ σ) (_hT : 0 ≤ T)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    ∀ v ∈ Set.Icc (-T) T,
      chen1973Lemma6Eq19OneSubSecondMoment x L level H (σ + v * I) ≤
        chen1973Lemma6Eq19I x L level *
          (2 * chen1973Lemma6Eq19SharpConstant *
              ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
              (1 + Real.log (H * H : ℕ)) ^ 4 +
            2 * (Q : ℝ) *
              chen1973Lemma6Eq19OneSubUniformEnvelope H Q σ T) := by
  intro v hv
  have hvabs : |v| ≤ T := (abs_le).2 hv
  have hnorm : ‖((σ : ℂ) + v * I)‖ ≤ |σ| + T := by
    calc
      ‖((σ : ℂ) + v * I)‖ ≤ ‖(σ : ℂ)‖ + ‖v * I‖ := norm_add_le _ _
      _ = |σ| + |v| := by simp
      _ ≤ |σ| + T := by linarith
  have hbase := chen1973Lemma6_eq19_oneSub_second_moment_fixed
    x L level H D Q (σ + v * I) hH hD hDQ (by simpa using hσ) hcell
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add_right
    apply mul_le_mul_of_nonneg_left
    · unfold chen1973Lemma6Eq19OneSubUniformEnvelope
      have hQ1 : 1 < Q := by omega
      have hlogQ : 0 ≤ Real.log (Q : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
      have hlogH : 0 ≤ 1 + Real.log (H : ℝ) :=
        add_nonneg zero_le_one
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ H by omega)))
      have hpow : 0 ≤ (((H + 1 : ℕ) : ℝ) ^ (-σ)) := by positivity
      have hleft : 0 ≤ 40 * ‖((σ : ℂ) + v * I)‖ * Real.sqrt Q *
          Real.log Q * (((H + 1 : ℕ) : ℝ) ^ (-((σ : ℂ) + v * I).re)) *
          (1 + Real.log H) := by positivity
      apply pow_le_pow_left₀ hleft
      have hre : ((σ : ℂ) + v * I).re = σ := by simp
      rw [hre]
      gcongr
    · norm_num
  · exact (chen1973Lemma6Eq19I_pos x L level).le

/-- A Cauchy-circle fourth-moment envelope uniform in the centre height. -/
def chen1973Lemma6Eq19CircleFourthEnvelopeUniform
    (Q : ℕ) (σ T r : ℝ) : ℝ :=
  21000000 * (Q : ℝ) ^ 2 * (|σ| + T + r) ^ 2 *
    Real.log ((Q : ℝ) * (1 + (|σ| + T + r))) ^ 4

/-- The actual `L'` fourth moment uniformly on a closed vertical interval.
Both the Cauchy radius and the scalar envelope are fixed outside `v`. -/
theorem chen1973Lemma6_eq19_LDeriv_fourth_moment_uniform
    (x L level Q : ℕ) (σ T r : ℝ) (hQ : 2 ≤ Q) (hT : 0 ≤ T)
    (hr : 0 < r)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q)
    (hspheres : ∀ v ∈ Set.Icc (-T) T, ∀ z ∈ Metric.sphere (σ + v * I) r,
      Chen1973Lemma3Domain z z.re z.im) :
    ∀ v ∈ Set.Icc (-T) T,
      chen1973Lemma6Eq19LDerivFourthMoment x L level (σ + v * I) ≤
        chen1973Lemma6Eq19I x L level * (Q : ℝ) *
          ((chen1973Lemma6Eq19CircleFourthEnvelopeUniform Q σ T r + 1) / r) ^ 4 := by
  intro v hv
  let s : ℂ := σ + v * I
  have hvabs : |v| ≤ T := (abs_le).2 hv
  have hnorm : ‖s‖ ≤ |σ| + T := by
    dsimp [s]
    calc
      ‖((σ : ℂ) + v * I)‖ ≤ ‖(σ : ℂ)‖ + ‖v * I‖ := norm_add_le _ _
      _ = |σ| + |v| := by simp
      _ ≤ |σ| + T := by linarith
  have hsum : 0 ≤ |σ| + T + r := by positivity
  have hargpos : 0 < (Q : ℝ) * (1 + (‖s‖ + r)) := by
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    positivity
  have hargle :
      (Q : ℝ) * (1 + (‖s‖ + r)) ≤
        (Q : ℝ) * (1 + (|σ| + T + r)) := by gcongr
  have hlogle := Real.log_le_log hargpos hargle
  have hlog0 : 0 ≤ Real.log ((Q : ℝ) * (1 + (‖s‖ + r))) := by
    apply Real.log_nonneg
    have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    nlinarith [norm_nonneg s]
  have hE : chen1973Lemma6Eq19CircleFourthEnvelope Q s r ≤
      chen1973Lemma6Eq19CircleFourthEnvelopeUniform Q σ T r := by
    unfold chen1973Lemma6Eq19CircleFourthEnvelope
      chen1973Lemma6Eq19CircleFourthEnvelopeUniform
    gcongr
  have hEU : 0 ≤ chen1973Lemma6Eq19CircleFourthEnvelopeUniform Q σ T r := by
    unfold chen1973Lemma6Eq19CircleFourthEnvelopeUniform
    positivity
  have hEOld : 0 ≤ chen1973Lemma6Eq19CircleFourthEnvelope Q s r := by
    unfold chen1973Lemma6Eq19CircleFourthEnvelope
    positivity
  have hbase := chen1973Lemma6_eq19_LDeriv_fourth_moment_cauchy
    x L level Q s r hQ hr hcell (hspheres v hv)
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀
    · exact div_nonneg (add_nonneg hEOld zero_le_one) hr.le
    · exact div_le_div_of_nonneg_right (by linarith [hE]) hr.le
  · exact mul_nonneg (chen1973Lemma6Eq19I_pos x L level).le (by positivity)

end AnalyticNumberTheory.LargeSieve
