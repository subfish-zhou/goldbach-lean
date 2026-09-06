/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19
import Mathlib.Analysis.Complex.Liouville

/-!
# Chen 1973, Lemma 6, equation (19): moment transport

This leaf pays the change from the squarefree equation-(17) weight
`|μ(d)| 3^ω(d) / d` to the reciprocal-totient weight used in (14), (15), and
Lemma 2.  It also applies the sharp, unconditional Lemma 2 to the literal prime-pair
polynomial.  The bounds stop at scalar moments and do not assume the final cell estimate.
-/

noncomputable section

open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- Public copy of the equation-(17) conductor weight. -/
def chen1973Lemma6Eq19Weight (d : ℕ) : ℝ :=
  |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
    (3 : ℝ) ^ d.primeFactors.card / d

/-- The coefficient obtained by collecting equal products in the literal pair
polynomial of equation (19). -/
def chen1973Lemma6Eq19PairCoefficient
    (x B k m : ℕ) (s : ℂ) (n : ℤ) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    if (pp.1 * pp.2 : ℤ) = n then
      1 / ((pp.1 * pp.2 : ℂ) ^ s *
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))
    else 0

lemma chen1973Lemma6_eq19Weight_nonneg (d : ℕ) :
    0 ≤ chen1973Lemma6Eq19Weight d := by
  unfold chen1973Lemma6Eq19Weight
  positivity

/-- Squarefreeness removes the Möbius absolute value, and `φ(d) ≤ d` changes
`1/d` to `1/φ(d)`.  This is the pointwise weight transport used in (19). -/
theorem chen1973Lemma6_eq19Weight_le_I_div_totient
    {x L level d : ℕ}
    (hd : d ∈ chen1973Lemma6ConductorBlock x L level) :
    chen1973Lemma6Eq19Weight d ≤
      chen1973Lemma6Eq19I x L level / (d.totient : ℝ) := by
  have hdprops : 0 < d ∧ Squarefree d := by
    have hmem := hd
    simp only [chen1973Lemma6ConductorBlock] at hmem
    split at hmem
    · rw [Finset.mem_filter] at hmem
      exact ⟨lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hmem.1).1,
        hmem.2.2⟩
    · simp only [chen1973Lemma6DyadicShell, Finset.mem_filter] at hmem
      exact ⟨lt_of_le_of_lt (Nat.zero_le _) hmem.1.2.1, hmem.2.2⟩
  obtain ⟨hdpos, hsquare⟩ := hdprops
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
    have hz := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsquare
    have hr : (((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 = 1 := by
      exact_mod_cast hz
    rcases sq_eq_one_iff.mp hr with h | h <;> simp [h]
  rw [chen1973Lemma6Eq19Weight, hmu, one_mul]
  have hthree := chen1973Lemma6_threePow_le_Eq19I hd
  have hφpos : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr hdpos
  have hφle : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  calc
    (3 : ℝ) ^ d.primeFactors.card / d ≤
        chen1973Lemma6Eq19I x L level / d := by gcongr
    _ ≤ chen1973Lemma6Eq19I x L level / d.totient := by
      exact div_le_div_of_nonneg_left
        (chen1973Lemma6Eq19I_pos x L level).le hφpos hφle

/-- Transport any nonnegative cell ledger to reciprocal-totient normalization. -/
theorem chen1973Lemma6_eq19_weight_transport
    {x L level : ℕ} (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        chen1973Lemma6Eq19Weight d * F d) ≤
      chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) * F d := by
  calc
    _ ≤ ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        (chen1973Lemma6Eq19I x L level / (d.totient : ℝ)) * F d := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right
        (chen1973Lemma6_eq19Weight_le_I_div_totient hd) (hF d)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

private lemma eq19_pair_product_mem
    {x B k m : ℕ} {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6PrimePairShell x B k m) :
    (pp.1 * pp.2 : ℤ) ∈ Finset.Icc (1 : ℤ) (x * x : ℕ) := by
  simp only [chen1973Lemma6PrimePairShell, chen1973Lemma6DyadicShell,
    Finset.mem_filter] at hpp
  have hp := hpp.1.1
  rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hp
  have hpRange := Finset.mem_product.mp hp.1
  have hp1 := Finset.mem_range.mp hpRange.1
  have hp2 := Finset.mem_range.mp hpRange.2
  have hprime1 := hp.2.1
  have hprime2 := hp.2.2.1
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast Nat.mul_pos hprime1.pos hprime2.pos
  · exact_mod_cast Nat.mul_le_mul (Nat.le_of_lt_succ hp1) (Nat.le_of_lt_succ hp2)

/-- Exact collection identity for the literal pair polynomial. -/
theorem chen1973Lemma6_eq19_pairPolynomial_eq_collected
    (x B k m : ℕ) (s : ℂ) {d : ℕ} (χ : PrimitiveCharacter d) :
    (∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
        ((pp.1 * pp.2 : ℂ) ^ s *
          Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))) =
      ∑ n ∈ Icc (1 : ℤ) (x * x : ℕ),
        chen1973Lemma6Eq19PairCoefficient x B k m s n * χ.1 (n : ZMod d) := by
  unfold chen1973Lemma6Eq19PairCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pp hpp
  let n : ℤ := pp.1 * pp.2
  have hn := eq19_pair_product_mem hpp
  rw [Finset.sum_eq_single n]
  · simp [n]
    ring
  · intro z hz hzne
    have hne : (pp.1 * pp.2 : ℤ) ≠ z := by
      simpa [n] using hzne.symm
    simp [hne]
  · exact fun h => False.elim (h hn)

/-- The actual pair-polynomial second moment on any source cell contained in
`(D,Q]`.  The constant comes from the proved sharp Lemma 2; no cell-bound premise
is accepted. -/
theorem chen1973Lemma6_eq19_pair_second_moment
    (x L level B k m D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    ∃ C : ℝ, 0 < C ∧
      chen1973Lemma6Eq19PairSecondMoment x L level B k m s ≤
        chen1973Lemma6Eq19I x L level *
          (2 * C * ((Q : ℝ) + ((x * x : ℕ) : ℝ) / D) *
            ∑ n ∈ Icc (1 : ℤ) (x * x : ℕ),
              ‖chen1973Lemma6Eq19PairCoefficient x B k m s n‖ ^ 2) := by
  obtain ⟨C, hC, hLS⟩ := chen1973Lemma2_equationThree_complex_unconditional
    (chen1973Lemma6Eq19PairCoefficient x B k m s) 0 (x * x) D Q hD
  refine ⟨C, hC, ?_⟩
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
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (by simpa only [Int.zero_add] using hLS)
        (chen1973Lemma6Eq19I_pos x L level).le

/-- Equation (14) transported to the literal equation-(19) weight and paid by
its unconditional explicit scalar endpoint. -/
theorem chen1973Lemma6_eq19_oneSub_second_moment
    (x L level H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D)
    (hDQ : D < Q) (hs : 1 ≤ s.re)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    ∃ C : ℝ, 0 < C ∧
      chen1973Lemma6Eq19OneSubSecondMoment x L level H s ≤
        chen1973Lemma6Eq19I x L level *
          (4 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
              (1 + Real.log (H * H : ℕ)) ^ 4 +
            2 * (Q : ℝ) *
              ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
                (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
                  (1 + Real.log H)) ^ 2) := by
  obtain ⟨C, hC, h14⟩ := chen1973Lemma6_equation14_final_scalar_paid
    H D Q s hH hD hDQ hs
  refine ⟨C, hC, ?_⟩
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
    _ ≤ _ := mul_le_mul_of_nonneg_left h14
      (chen1973Lemma6Eq19I_pos x L level).le

/-- Equation (15) transported to the literal equation-(19) weight and paid by
its unconditional divisor-energy scalar endpoint. -/
theorem chen1973Lemma6_eq19_mobius_fourth_moment
    (x L level H D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hs : Chen1973Lemma3Domain s s.re s.im)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    ∃ C : ℝ, 0 < C ∧
      chen1973Lemma6Eq19MobiusFourthMoment x L level H s ≤
        chen1973Lemma6Eq19I x L level *
          (2 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
            (1 + Real.log (H * H : ℕ)) ^ 4) := by
  obtain ⟨C, hC, h15⟩ := chen1973Lemma6_equation15_final_log_power
    H D Q s hD hs
  refine ⟨C, hC, ?_⟩
  unfold chen1973Lemma6Eq19MobiusFourthMoment
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
      chen1973Lemma6Eq19Weight d *
        ∑ χ : PrimitiveCharacter d,
          ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4) ≤ _
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter d,
              ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4 := by
      apply chen1973Lemma6_eq19_weight_transport
      intro d
      positivity
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hcell
        intro d hd hdnot
        positivity
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ ≤ _ := mul_le_mul_of_nonneg_left h15
      (chen1973Lemma6Eq19I_pos x L level).le

/-- A nonnegative scalar envelope for the corrected Lemma 3 fourth moment
on the Cauchy circle of radius `r` about `s`. -/
def chen1973Lemma6Eq19CircleFourthEnvelope (Q : ℕ) (s : ℂ) (r : ℝ) : ℝ :=
  21000000 * (Q : ℝ) ^ 2 * (‖s‖ + r) ^ 2 *
    Real.log ((Q : ℝ) * (1 + (‖s‖ + r))) ^ 4

private lemma norm_le_fourthEnvelope_add_one {y E : ℝ}
    (hy : 0 ≤ y) (hE : 0 ≤ E) (h : y ^ 4 ≤ E) : y ≤ E + 1 := by
  by_cases hy1 : y ≤ 1
  · linarith
  · have hone : 1 < y := lt_of_not_ge hy1
    have hyy : y ≤ y ^ 4 := by nlinarith [sq_nonneg y, sq_nonneg (y ^ 2 - y)]
    linarith

/-- The actual `L'` fourth moment on an equation-(17) cell, obtained by Cauchy's
circle estimate from the unconditional corrected Lemma 3.  The deliberately
coarse extra factor `Q` only counts reciprocal-totient-normalized character
families; all constants and the circle range are explicit. -/
theorem chen1973Lemma6_eq19_LDeriv_fourth_moment_cauchy
    (x L level Q : ℕ) (s : ℂ) (r : ℝ) (hQ : 2 ≤ Q) (hr : 0 < r)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q)
    (hsphere : ∀ z ∈ Metric.sphere s r,
      Chen1973Lemma3Domain z z.re z.im) :
    chen1973Lemma6Eq19LDerivFourthMoment x L level s ≤
      chen1973Lemma6Eq19I x L level * (Q : ℝ) *
        ((chen1973Lemma6Eq19CircleFourthEnvelope Q s r + 1) / r) ^ 4 := by
  let E := chen1973Lemma6Eq19CircleFourthEnvelope Q s r
  have hT : 0 ≤ ‖s‖ + r := by positivity
  have harg : 1 < (Q : ℝ) * (1 + (‖s‖ + r)) := by
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith [norm_nonneg s]
  have hE : 0 ≤ E := by
    dsimp [E, chen1973Lemma6Eq19CircleFourthEnvelope]
    positivity
  have hderiv : ∀ d ∈ chen1973Lemma6ConductorBlock x L level,
      ∀ χ : PrimitiveCharacter d,
        ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4 ≤ ((E + 1) / r) ^ 4 := by
    intro d hd χ
    have hdI := Finset.mem_Icc.mp (hcell hd)
    have hd1 : 1 < d := by omega
    letI : NeZero d := ⟨Nat.ne_zero_of_lt hd1⟩
    have hχ : χ.1 ≠ 1 := chen1973_primitive_ne_one hd1 χ
    have hcircle : ∀ z ∈ Metric.sphere s r, ‖χ.1.LFunction z‖ ≤ E + 1 := by
      intro z hz
      have hzs : ‖z‖ ≤ ‖s‖ + r := by
        have hdist : dist z s = r := hz
        calc
          ‖z‖ ≤ ‖s‖ + ‖z - s‖ := by
            have := norm_add_le s (z - s)
            simpa [add_sub_cancel_left] using this
          _ = ‖s‖ + r := by rw [← dist_eq_norm, hdist]
      have hzdom := hsphere z hz
      have hfour := chen1973Lemma3_corrected_endpoint_unconditional z hQ hzdom
      have hterm : ‖chen1973PrimitiveLValue d z χ‖ ^ 4 ≤
          chen1973Lemma3FourthMoment Q z := by
        unfold chen1973Lemma3FourthMoment
        calc
          ‖chen1973PrimitiveLValue d z χ‖ ^ 4 ≤
              ∑ ψ : PrimitiveCharacter d,
                ‖chen1973PrimitiveLValue d z ψ‖ ^ 4 := by
            exact Finset.single_le_sum (s := Finset.univ)
              (f := fun ψ : PrimitiveCharacter d =>
                ‖chen1973PrimitiveLValue d z ψ‖ ^ 4)
              (fun ψ hψ => by positivity) (Finset.mem_univ χ)
          _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ ψ : PrimitiveCharacter q,
                ‖chen1973PrimitiveLValue q z ψ‖ ^ 4 := by
            exact Finset.single_le_sum (s := Finset.Icc 1 Q)
              (f := fun q => ∑ ψ : PrimitiveCharacter q,
                ‖chen1973PrimitiveLValue q z ψ‖ ^ 4)
              (fun q hq => Finset.sum_nonneg fun ψ hψ => by positivity)
              (Finset.mem_Icc.mpr ⟨by omega, hdI.2⟩)
      have hlogmono :
          Real.log ((Q : ℝ) * (1 + ‖z‖)) ≤
            Real.log ((Q : ℝ) * (1 + (‖s‖ + r))) := by
        apply Real.log_le_log
        · positivity
        · gcongr
      have hzlog0 : 0 ≤ Real.log ((Q : ℝ) * (1 + ‖z‖)) := by
        apply Real.log_nonneg
        have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
        nlinarith [norm_nonneg z]
      have hbound : ‖chen1973PrimitiveLValue d z χ‖ ^ 4 ≤ E := by
        calc
          _ ≤ chen1973Lemma3FourthMoment Q z := hterm
          _ ≤ 21000000 * (Q : ℝ) ^ 2 * ‖z‖ ^ 2 *
              Real.log ((Q : ℝ) * (1 + ‖z‖)) ^ 4 := hfour
          _ ≤ 21000000 * (Q : ℝ) ^ 2 * (‖s‖ + r) ^ 2 *
              Real.log ((Q : ℝ) * (1 + (‖s‖ + r))) ^ 4 := by
                gcongr
          _ = E := rfl
      have hvalue : chen1973PrimitiveLValue d z χ = χ.1.LFunction z := by
        simp [chen1973PrimitiveLValue, hd1]
      rw [hvalue] at hbound
      exact norm_le_fourthEnvelope_add_one (norm_nonneg _) hE hbound
    have hdiff : DiffContOnCl ℂ χ.1.LFunction (Metric.ball s r) :=
      (χ.1.differentiable_LFunction hχ).diffContOnCl
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff hcircle
    have hnon : 0 ≤ ‖deriv χ.1.LFunction s‖ := norm_nonneg _
    have hp := pow_le_pow_left₀ hnon hc 4
    simp only [chen1973PrimitiveLDeriv, dif_pos hd1]
    simpa [div_eq_mul_inv] using hp
  unfold chen1973Lemma6Eq19LDerivFourthMoment
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
      chen1973Lemma6Eq19Weight d *
        ∑ χ : PrimitiveCharacter d, ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4) ≤ _
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter d,
              ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4 := by
      apply chen1973Lemma6_eq19_weight_transport
      intro d
      positivity
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          ((E + 1) / r) ^ 4 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro d hd
        have hdI := Finset.mem_Icc.mp (hcell hd)
        have hdpos : 0 < d := by omega
        have hφpos : (0 : ℝ) < d.totient := by
          exact_mod_cast Nat.totient_pos.mpr hdpos
        have hcardNat : Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
          letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
          calc
            Fintype.card (PrimitiveCharacter d) ≤
                Fintype.card (DirichletCharacter ℂ d) :=
              @Fintype.card_subtype_le (DirichletCharacter ℂ d) _
                (fun χ => χ.IsPrimitive) _
            _ = d.totient := by
              have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
                (a := (1 : ZMod d)) isUnit_one (1 : ZMod d)
              simpa using h
        calc
          (1 / (d.totient : ℝ)) *
              ∑ χ : PrimitiveCharacter d,
                ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4 ≤
            (1 / (d.totient : ℝ)) *
              ∑ _χ : PrimitiveCharacter d, ((E + 1) / r) ^ 4 := by
                apply mul_le_mul_of_nonneg_left
                · apply Finset.sum_le_sum
                  intro χ hχmem
                  exact hderiv d hd χ
                · positivity
          _ = ((Fintype.card (PrimitiveCharacter d) : ℝ) /
              (d.totient : ℝ)) * ((E + 1) / r) ^ 4 := by simp; ring
          _ ≤ ((E + 1) / r) ^ 4 := by
            have hratio : (Fintype.card (PrimitiveCharacter d) : ℝ) /
                (d.totient : ℝ) ≤ 1 := by
              rw [div_le_one hφpos]
              exact_mod_cast hcardNat
            exact mul_le_of_le_one_left (by positivity) hratio
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ = chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6ConductorBlock x L level).card *
          ((E + 1) / r) ^ 4 := by simp; ring
    _ ≤ chen1973Lemma6Eq19I x L level * (Q : ℝ) *
          ((E + 1) / r) ^ 4 := by
      have hcardNat :
          (chen1973Lemma6ConductorBlock x L level).card ≤ Q := calc
        (chen1973Lemma6ConductorBlock x L level).card ≤
            (Finset.Icc 2 Q).card := Finset.card_le_card hcell
        _ ≤ Q := by simp
      have hcardReal :
          ((chen1973Lemma6ConductorBlock x L level).card : ℝ) ≤ Q := by
        exact_mod_cast hcardNat
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardReal
          (chen1973Lemma6Eq19I_pos x L level).le) (by positivity)

end AnalyticNumberTheory.LargeSieve
