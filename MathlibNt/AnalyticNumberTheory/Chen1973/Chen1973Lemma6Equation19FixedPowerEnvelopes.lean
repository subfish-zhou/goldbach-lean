/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17CorrectedKernel
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19Final
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19UniformMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (19): fixed-power infinite-height envelopes

The alpha lane uses the `21/10` corrected-kernel weakening after the square root
of equation (14), hence only linear height growth.  The beta lane keeps the
literal multiplicative `2,4,4` Hölder estimate and takes the genuine fourth
root of the Lemma-3 fourth moment before using the fourth-power kernel
weakening.  No final `H`/logarithm absorption is performed here.
-/

noncomputable section
set_option maxHeartbeats 1600000

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The fixed (height-independent) pair-energy bound. -/
def chen1973Lemma6Eq19FixedPairBound
    (x L level B k m D Q : ℕ) (σ : ℝ) : ℝ :=
  chen1973Lemma6Eq19I x L level *
    (chen1973Lemma6Eq19SharpConstant *
      ((Q : ℝ) + ((x * x : ℕ) : ℝ) / D) *
      ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6Eq19PairAtom x (σ : ℂ) pp‖ ^ 2)

private lemma eq19_pairAtom_norm_vertical_general
    {x B k m : ℕ} {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6PrimePairShell x B k m) (σ v : ℝ) :
    ‖chen1973Lemma6Eq19PairAtom x (σ + v * I) pp‖ =
      ‖chen1973Lemma6Eq19PairAtom x (σ : ℂ) pp‖ := by
  unfold chen1973Lemma6Eq19PairAtom
  simp only [chen1973Lemma6PrimePairShell, chen1973Lemma6DyadicShell,
    Finset.mem_filter] at hpp
  have hpair := hpp.1.1
  rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hpair
  have hp₁ : 0 < pp.1 := hpair.2.1.pos
  have hp₂ : 0 < pp.2 := hpair.2.2.1.pos
  have hcpow :
      ‖((pp.1 * pp.2 : ℂ) ^ ((σ : ℂ) + v * I))‖ =
        ‖((pp.1 * pp.2 : ℂ) ^ (σ : ℂ))‖ := by
    have hpos : 0 < (pp.1 : ℝ) * (pp.2 : ℝ) := by exact_mod_cast Nat.mul_pos hp₁ hp₂
    have h₁ := Complex.norm_cpow_eq_rpow_re_of_pos
      (x := (pp.1 : ℝ) * (pp.2 : ℝ)) (y := ((σ : ℂ) + v * I)) hpos
    have h₂ := Complex.norm_cpow_eq_rpow_re_of_pos
      (x := (pp.1 : ℝ) * (pp.2 : ℝ)) (y := (σ : ℂ)) hpos
    rw [show (((σ : ℂ) + v * I).re) = σ by simp] at h₁
    rw [show ((σ : ℂ).re) = σ by simp] at h₂
    simpa using h₁.trans h₂.symm
  simp only [norm_div, norm_one, norm_mul]
  rw [hcpow]

/-- The pair second moment is uniformly bounded on the whole vertical line. -/
theorem chen1973Lemma6_eq19_pair_second_moment_fixed_height
    (x L level B k m D Q : ℕ) (σ v : ℝ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq19PairSecondMoment x L level B k m (σ + v * I) ≤
      chen1973Lemma6Eq19FixedPairBound x L level B k m D Q σ := by
  have h := chen1973Lemma6_eq19_pair_second_moment_fixed
    x L level B k m D Q (σ + v * I) hD hcell
  unfold chen1973Lemma6Eq19FixedPairBound
  have hsum :
      (∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6Eq19PairAtom x (σ + v * I) pp‖ ^ 2) =
      ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6Eq19PairAtom x (σ : ℂ) pp‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro pp hpp
    rw [eq19_pairAtom_norm_vertical_general hpp σ v]
  simpa [hsum] using h

/-- Sharp fourth-root Cauchy envelope for the `L'` fourth moment.  Unlike the
older compatibility bound, the fourth moment from Lemma 3 is not first weakened
to a first-power pointwise bound. -/
theorem chen1973Lemma6_eq19_LDeriv_fourth_moment_sharp_cauchy
    (x L level Q : ℕ) (s : ℂ) (r : ℝ) (hQ : 2 ≤ Q) (hr : 0 < r)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q)
    (hsphere : ∀ z ∈ Metric.sphere s r,
      Chen1973Lemma3Domain z z.re z.im) :
    chen1973Lemma6Eq19LDerivFourthMoment x L level s ≤
      chen1973Lemma6Eq19I x L level * (Q : ℝ) *
        ((Real.sqrt (Real.sqrt
          (chen1973Lemma6Eq19CircleFourthEnvelope Q s r + 1))) / r) ^ 4 := by
  let E := chen1973Lemma6Eq19CircleFourthEnvelope Q s r
  have hderiv : ∀ d ∈ chen1973Lemma6ConductorBlock x L level,
      ∀ χ : PrimitiveCharacter d,
        ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4 ≤
          (Real.sqrt (Real.sqrt (E + 1)) / r) ^ 4 := by
    intro d hd χ
    have hdI := Finset.mem_Icc.mp (hcell hd)
    have hd1 : 1 < d := by omega
    letI : NeZero d := ⟨Nat.ne_zero_of_lt hd1⟩
    have hχ : χ.1 ≠ 1 := chen1973_primitive_ne_one hd1 χ
    have hcircle : ∀ z ∈ Metric.sphere s r,
        ‖χ.1.LFunction z‖ ≤ Real.sqrt (Real.sqrt (E + 1)) := by
      intro z hz
      have hzs : ‖z‖ ≤ ‖s‖ + r := by
        have hdist : dist z s = r := hz
        calc
          ‖z‖ ≤ ‖s‖ + ‖z - s‖ := by
            have ht := norm_add_le s (z - s)
            simpa [add_sub_cancel_left] using ht
          _ = ‖s‖ + r := by rw [← dist_eq_norm, hdist]
      have hfour := chen1973Lemma3_corrected_endpoint_unconditional z hQ (hsphere z hz)
      have hterm : ‖chen1973PrimitiveLValue d z χ‖ ^ 4 ≤
          chen1973Lemma3FourthMoment Q z := by
        unfold chen1973Lemma3FourthMoment
        calc
          _ ≤ ∑ ψ : PrimitiveCharacter d,
              ‖chen1973PrimitiveLValue d z ψ‖ ^ 4 :=
            Finset.single_le_sum (s := Finset.univ) (fun ψ hψ => by positivity)
              (Finset.mem_univ χ)
          _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ ψ : PrimitiveCharacter q,
              ‖chen1973PrimitiveLValue q z ψ‖ ^ 4 :=
            Finset.single_le_sum (s := Finset.Icc 1 Q)
              (f := fun q => ∑ ψ : PrimitiveCharacter q,
                ‖chen1973PrimitiveLValue q z ψ‖ ^ 4)
              (fun q hq => Finset.sum_nonneg fun ψ hψ =>
                (show 0 ≤ ‖chen1973PrimitiveLValue q z ψ‖ ^ 4 by positivity))
              (Finset.mem_Icc.mpr ⟨by omega, hdI.2⟩)
      have hargpos : 0 < (Q : ℝ) * (1 + ‖z‖) := by positivity
      have hlogmono :
          Real.log ((Q : ℝ) * (1 + ‖z‖)) ≤
            Real.log ((Q : ℝ) * (1 + (‖s‖ + r))) := by
        exact Real.log_le_log hargpos (by gcongr)
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
              Real.log ((Q : ℝ) * (1 + (‖s‖ + r))) ^ 4 := by gcongr
          _ = E := rfl
      have hvalue : chen1973PrimitiveLValue d z χ = χ.1.LFunction z := by
        simp [chen1973PrimitiveLValue, hd1]
      rw [hvalue] at hbound
      apply Real.le_sqrt_of_sq_le
      apply Real.le_sqrt_of_sq_le
      simpa only [← pow_mul] using hbound.trans (le_add_of_nonneg_right zero_le_one)
    have hdiff : DiffContOnCl ℂ χ.1.LFunction (Metric.ball s r) :=
      (χ.1.differentiable_LFunction hχ).diffContOnCl
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff hcircle
    have hp := pow_le_pow_left₀ (norm_nonneg _) hc 4
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
            ∑ χ : PrimitiveCharacter d, ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4 := by
      apply chen1973Lemma6_eq19_weight_transport
      intro d
      positivity
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (Real.sqrt (Real.sqrt (E + 1)) / r) ^ 4 := by
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
              have ht := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
                (a := (1 : ZMod d)) isUnit_one (1 : ZMod d)
              simpa using ht
        calc
          (1 / (d.totient : ℝ)) *
              ∑ χ : PrimitiveCharacter d, ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4 ≤
            (1 / (d.totient : ℝ)) *
              ∑ _χ : PrimitiveCharacter d,
                (Real.sqrt (Real.sqrt (E + 1)) / r) ^ 4 := by
              apply mul_le_mul_of_nonneg_left
              · apply Finset.sum_le_sum
                intro χ hχmem
                exact hderiv d hd χ
              · positivity
          _ = ((Fintype.card (PrimitiveCharacter d) : ℝ) /
              (d.totient : ℝ)) *
                (Real.sqrt (Real.sqrt (E + 1)) / r) ^ 4 := by simp; ring
          _ ≤ (Real.sqrt (Real.sqrt (E + 1)) / r) ^ 4 := by
            have hratio : (Fintype.card (PrimitiveCharacter d) : ℝ) /
                (d.totient : ℝ) ≤ 1 := by
              rw [div_le_one hφpos]
              exact_mod_cast hcardNat
            exact mul_le_of_le_one_left (by positivity) hratio
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ = chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6ConductorBlock x L level).card *
          (Real.sqrt (Real.sqrt (E + 1)) / r) ^ 4 := by simp; ring
    _ ≤ chen1973Lemma6Eq19I x L level * (Q : ℝ) *
          (Real.sqrt (Real.sqrt (E + 1)) / r) ^ 4 := by
      have hcardNat : (chen1973Lemma6ConductorBlock x L level).card ≤ Q := calc
        _ ≤ (Finset.Icc 2 Q).card := Finset.card_le_card hcell
        _ ≤ Q := by simp
      have hcardReal :
          ((chen1973Lemma6ConductorBlock x L level).card : ℝ) ≤ Q := by
        exact_mod_cast hcardNat
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardReal
          (chen1973Lemma6Eq19I_pos x L level).le) (by positivity)
    _ = _ := rfl

/-- Fixed coefficient left after extracting the alpha lane's single power of
`1+v` from the square root of equation (14). -/
def chen1973Lemma6Eq19FirstFixedPower
    (x L level B k m H D Q : ℕ) (σ : ℝ) : ℝ :=
  Real.sqrt (chen1973Lemma6Eq19FixedPairBound x L level B k m D Q σ) *
    Real.sqrt (chen1973Lemma6Eq19I x L level *
      (2 * chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (1 + Real.log (H * H : ℕ)) ^ 4 +
        2 * (Q : ℝ) *
          ((40 * (|σ| + 1) * Real.sqrt Q * Real.log Q *
            (((H + 1 : ℕ) : ℝ) ^ (-σ))) * (1 + Real.log H)) ^ 2))

/-- The first numerator has genuinely linear, rather than postulated, height
growth. -/
theorem chen1973Lemma6_eq19_first_le_fixedPower
    (x L level B k m H D Q : ℕ) (σ v : ℝ)
    (hH : 0 < H) (hD : 0 < D) (hDQ : D < Q) (hσ : 1 ≤ σ)
    (hv : 0 ≤ v)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6A x L level B k m H (σ + v * I) ≤
      chen1973Lemma6Eq19FirstFixedPower x L level B k m H D Q σ * (1 + v) := by
  let P := chen1973Lemma6Eq19FixedPairBound x L level B k m D Q σ
  let R := chen1973Lemma6Eq19I x L level *
      (2 * chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (1 + Real.log (H * H : ℕ)) ^ 4 +
        2 * (Q : ℝ) *
          ((40 * (|σ| + 1) * Real.sqrt Q * Real.log Q *
            (((H + 1 : ℕ) : ℝ) ^ (-σ))) * (1 + Real.log H)) ^ 2)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hP : 0 ≤ P := by
    dsimp [P, chen1973Lemma6Eq19FixedPairBound]
    exact mul_nonneg (chen1973Lemma6Eq19I_pos x L level).le
      (mul_nonneg
        (mul_nonneg chen1973Lemma6_eq19SharpConstant_pos.le
          (add_nonneg (by positivity) (div_nonneg (by positivity) hDR.le)))
        (Finset.sum_nonneg fun pp hpp => by positivity))
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (chen1973Lemma6Eq19I_pos x L level).le
      (add_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) chen1973Lemma6_eq19SharpConstant_pos.le)
            (add_nonneg (by positivity) (div_nonneg (by positivity) hDR.le))) (by positivity))
        (by positivity))
  have ht : 0 ≤ 1 + v := by linarith
  have hp := chen1973Lemma6_eq19_pair_second_moment_fixed_height
    x L level B k m D Q σ v hD hcell
  have ho := chen1973Lemma6_eq19_oneSub_second_moment_uniform
    x L level H D Q σ v hH hD hDQ hσ hv hcell v (by constructor <;> linarith)
  have hlin : |σ| + v ≤ (|σ| + 1) * (1 + v) := by
    nlinarith [abs_nonneg σ]
  have hinside :
      chen1973Lemma6Eq19OneSubSecondMoment x L level H (σ + v * I) ≤
        R * (1 + v) ^ 2 := by
    refine ho.trans ?_
    dsimp [R, chen1973Lemma6Eq19OneSubUniformEnvelope]
    have hlogH : 0 ≤ 1 + Real.log (H : ℝ) := by
      have hH1 : 1 ≤ H := by omega
      positivity
    have hfac : 0 ≤ 40 * Real.sqrt Q * Real.log Q *
        (((H + 1 : ℕ) : ℝ) ^ (-σ)) * (1 + Real.log H) := by positivity
    have hsq :
        ((40 * (|σ| + v) * Real.sqrt Q * Real.log Q *
          (((H + 1 : ℕ) : ℝ) ^ (-σ))) * (1 + Real.log H)) ^ 2 ≤
        ((40 * (|σ| + 1) * Real.sqrt Q * Real.log Q *
          (((H + 1 : ℕ) : ℝ) ^ (-σ))) * (1 + Real.log H)) ^ 2 *
          (1 + v) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hlin hfac
      have hpw := pow_le_pow_left₀ (by positivity : 0 ≤ (|σ| + v) *
        (40 * Real.sqrt Q * Real.log Q * (((H + 1 : ℕ) : ℝ) ^ (-σ)) *
          (1 + Real.log H))) hm 2
      nlinarith
    have ht1 : 1 ≤ (1 + v) ^ 2 := by nlinarith
    have hbase : 0 ≤ 2 * chen1973Lemma6Eq19SharpConstant *
        ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
        (1 + Real.log (H * H : ℕ)) ^ 4 := by
      have hHH : (1 : ℝ) ≤ (H * H : ℕ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hH.ne' hH.ne'))
      have hlogHH : 0 ≤ Real.log (H * H : ℕ) := Real.log_nonneg hHH
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) chen1973Lemma6_eq19SharpConstant_pos.le)
          (add_nonneg (by positivity) (div_nonneg (by positivity) hDR.le)))
        (pow_nonneg (by linarith) 4)
    have hI := (chen1973Lemma6Eq19I_pos x L level).le
    have hterm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * (Q : ℝ) from by positivity)
    have hraw :
        2 * chen1973Lemma6Eq19SharpConstant *
              ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
              (1 + Real.log (H * H : ℕ)) ^ 4 +
            2 * (Q : ℝ) *
              ((40 * (|σ| + v) * Real.sqrt Q * Real.log Q *
                (((H + 1 : ℕ) : ℝ) ^ (-σ))) * (1 + Real.log H)) ^ 2 ≤
          (2 * chen1973Lemma6Eq19SharpConstant *
              ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
              (1 + Real.log (H * H : ℕ)) ^ 4 +
            2 * (Q : ℝ) *
              ((40 * (|σ| + 1) * Real.sqrt Q * Real.log Q *
                (((H + 1 : ℕ) : ℝ) ^ (-σ))) * (1 + Real.log H)) ^ 2) *
            (1 + v) ^ 2 := by
      simpa only [add_mul, mul_assoc] using
        add_le_add (le_mul_of_one_le_right hbase ht1) hterm
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hraw hI
  have hsqrtO :
      Real.sqrt (chen1973Lemma6Eq19OneSubSecondMoment x L level H (σ + v * I)) ≤
        Real.sqrt R * (1 + v) := by
    have hs := Real.sqrt_le_sqrt hinside
    rw [Real.sqrt_mul hR, Real.sqrt_sq_eq_abs, abs_of_nonneg ht] at hs
    exact hs
  have hbase := chen1973Lemma6A_le_moment_product x L level B k m H (σ + v * I)
  unfold chen1973Lemma6Eq19FirstFixedPower
  change _ ≤ Real.sqrt P * Real.sqrt R * (1 + v)
  exact hbase.trans (by
    calc
      _ ≤ Real.sqrt P * (Real.sqrt R * (1 + v)) :=
        mul_le_mul (Real.sqrt_le_sqrt hp) hsqrtO (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
      _ = _ := by ring)

/-- The two fixed decay profiles used below. -/
def chen1973Lemma6Eq19LinearDecay (v : ℝ) : ℝ :=
  (1 + v) / (1 + |v| ^ ((21 : ℝ) / 10))

def chen1973Lemma6Eq19QuadraticDecay (v : ℝ) : ℝ :=
  (1 + v) ^ (2 : ℕ) / (1 + |v| ^ (4 : ℕ))

/-- The alpha fixed-power profile is integrable on the positive half-line. -/
theorem chen1973Lemma6_eq19_linearDecay_integrable :
    IntegrableOn chen1973Lemma6Eq19LinearDecay (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · apply (show Continuous chen1973Lemma6Eq19LinearDecay by
      unfold chen1973Lemma6Eq19LinearDecay
      refine Continuous.div (continuous_const.add continuous_id)
        (continuous_const.add (continuous_abs.rpow_const (by norm_num))) ?_
      intro v
      positivity).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set
    exact Ioc_subset_Icc_self
  · have hpow : IntegrableOn (fun v : ℝ => 2 * v ^ (-(11 : ℝ) / 10)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 2
    apply Integrable.mono' hpow
    · exact (show Continuous chen1973Lemma6Eq19LinearDecay by
        unfold chen1973Lemma6Eq19LinearDecay
        refine Continuous.div (continuous_const.add continuous_id)
          (continuous_const.add (continuous_abs.rpow_const (by norm_num))) ?_
        intro v
        positivity).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := zero_lt_one.trans hv
      have hv1 : 1 ≤ v := hv.le
      have hnum : 1 + v ≤ 2 * v := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        unfold chen1973Lemma6Eq19LinearDecay; positivity),
        chen1973Lemma6Eq19LinearDecay, abs_of_pos hv0]
      calc
        (1 + v) / (1 + v ^ ((21 : ℝ) / 10)) ≤
            (2 * v) / v ^ ((21 : ℝ) / 10) := by
          exact div_le_div₀ (by positivity) hnum (Real.rpow_pos_of_pos hv0 _)
            (by linarith)
        _ = 2 * v ^ (-(11 : ℝ) / 10) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hv0.le]
          calc
            2 * v * v ^ (-(21 / 10 : ℝ)) =
                2 * (v ^ (1 : ℝ) * v ^ (-(21 / 10 : ℝ))) := by
              rw [Real.rpow_one]
              ring
            _ = 2 * v ^ ((1 : ℝ) + (-(21 / 10 : ℝ))) := by
              rw [Real.rpow_add hv0]
            _ = 2 * v ^ (-(11 : ℝ) / 10) := by norm_num

/-- The corrected Perron kernel has the fixed linear-growth decay bound. -/
theorem chen1973Lemma6_eq17_correctedKernel_inv_le_linearDecay
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ)
    (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
      (2 * Real.log x ^ ((231 : ℝ) / 100) / σ) /
        (1 + |v| ^ ((21 : ℝ) / 10)) := by
  have hfac := chen1973Lemma6_eq17_correctedFactor_vertical_inv_le_21_div_10 hx σ v horder
  have hnorm : σ ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    calc
      σ = |((σ : ℂ) + (v : ℂ) * I).re| := by simp [abs_of_pos hσ]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hcalc :
      ‖((σ : ℂ) + (v : ℂ) * I)‖⁻¹ *
          (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
            chen1973PerronScale (x : ℝ)) ^
              (chen1973PerronOrder (x : ℝ) + 1))⁻¹ ≤
      σ⁻¹ * (2 * Real.log x ^ ((231 : ℝ) / 100) /
        (1 + |v| ^ ((21 : ℝ) / 10))) := by
    have hfac0 : 0 ≤
        (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
          chen1973PerronScale (x : ℝ)) ^
            (chen1973PerronOrder (x : ℝ) + 1))⁻¹ := by
      apply inv_nonneg.mpr
      have hscale : 0 < chen1973PerronScale (x : ℝ) :=
        chen1973Lemma6_eq17_perronScale_pos (by omega)
      linarith [pow_nonneg
        (div_nonneg (norm_nonneg ((σ : ℂ) + (v : ℂ) * I)) hscale.le)
        (chen1973PerronOrder (x : ℝ) + 1)]
    exact mul_le_mul (inv_anti₀ hσ hnorm) hfac hfac0 (inv_nonneg.mpr hσ.le)
  simpa [chen1973Lemma6Eq17CorrectedKernel, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hcalc

private theorem eq19_corrected_inv_le_21
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ)
    (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
      (2 * Real.log x ^ ((231 : ℝ) / 100) / σ) /
        (1 + |v| ^ ((21 : ℝ) / 10)) := by
  exact chen1973Lemma6_eq17_correctedKernel_inv_le_linearDecay hx hσ horder

/-- Explicit alpha-envelope integral, with no continuity or growth premise. -/
theorem chen1973Lemma6_eq19_first_fixedPower_integrable_and_bound
    (x L level B k m H D Q : ℕ) (σ : ℝ)
    (hx : 3 ≤ x) (hH : 0 < H) (hD : 0 < D) (hDQ : D < Q)
    (hσ : 1 ≤ σ) (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    let F := fun v : ℝ =>
      chen1973Lemma6Eq19FirstFixedPower x L level B k m H D Q σ * (1 + v) /
        chen1973Lemma6Eq17CorrectedKernel x (σ + v * I)
    IntegrableOn F (Ioi 0) ∧
      (∫ v in Ioi (0 : ℝ), F v) ≤
        (2 * Real.log x ^ ((231 : ℝ) / 100) / σ) *
          chen1973Lemma6Eq19FirstFixedPower x L level B k m H D Q σ *
          ∫ v in Ioi (0 : ℝ), chen1973Lemma6Eq19LinearDecay v := by
  dsimp
  let G := chen1973Lemma6Eq19FirstFixedPower x L level B k m H D Q σ
  have hG : 0 ≤ G := by dsimp [G, chen1973Lemma6Eq19FirstFixedPower]; positivity
  let C := 2 * Real.log x ^ ((231 : ℝ) / 100) / σ
  have hmajor : IntegrableOn (fun v => C * G * chen1973Lemma6Eq19LinearDecay v) (Ioi 0) :=
    chen1973Lemma6_eq19_linearDecay_integrable.const_mul (C * G)
  have hint : IntegrableOn (fun v : ℝ =>
      G * (1 + v) / chen1973Lemma6Eq17CorrectedKernel x (σ + v * I)) (Ioi 0) := by
    apply Integrable.mono' hmajor
    · apply Continuous.aestronglyMeasurable
      apply Continuous.div
      · fun_prop
      · unfold chen1973Lemma6Eq17CorrectedKernel
        fun_prop
      · intro v
        exact (chen1973Lemma6_eq17_correctedKernel_pos (by omega : 1 < x)
          (lt_of_lt_of_le zero_lt_one hσ)).ne'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := hv
      have hk := chen1973Lemma6_eq17_correctedKernel_pos
        (x := x) (v := v) (by omega : 1 < x) (lt_of_lt_of_le zero_lt_one hσ)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hG (by linarith)) hk.le),
        div_eq_mul_inv]
      have hi := eq19_corrected_inv_le_21 hx (v := v)
        (lt_of_lt_of_le zero_lt_one hσ) horder
      calc
        G * (1 + v) * (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
            G * (1 + v) * (C / (1 + |v| ^ ((21 : ℝ) / 10))) :=
          mul_le_mul_of_nonneg_left (by simpa [C] using hi)
            (mul_nonneg hG (by linarith))
        _ = C * G * chen1973Lemma6Eq19LinearDecay v := by
          unfold chen1973Lemma6Eq19LinearDecay
          ring
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ v in Ioi (0 : ℝ), C * G * chen1973Lemma6Eq19LinearDecay v := by
      apply integral_mono_ae hint hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := hv
      rw [div_eq_mul_inv]
      have hi := eq19_corrected_inv_le_21 hx (v := v)
        (lt_of_lt_of_le zero_lt_one hσ) horder
      exact (mul_le_mul_of_nonneg_left (by simpa [C] using hi)
        (mul_nonneg hG (by linarith))).trans_eq (by
          unfold chen1973Lemma6Eq19LinearDecay; ring)
    _ = C * G * ∫ v in Ioi (0 : ℝ), chen1973Lemma6Eq19LinearDecay v := by
      rw [MeasureTheory.integral_const_mul]

/-- A height-independent polynomial majorant for the Lemma-3 circle envelope.
The two nested square roots of this quantity are deliberately retained in the
beta-lane coefficient. -/
def chen1973Lemma6Eq19SecondCircleFixedPower (Q : ℕ) (σ r : ℝ) : ℝ :=
  21000000 * (Q : ℝ) ^ 6 * (1 + |σ| + r) ^ 6 + 1

private theorem eq19_circleEnvelope_le_fixedPower
    (Q : ℕ) (σ r v : ℝ) (hQ : 2 ≤ Q) (hr : 0 < r) (hv : 0 ≤ v) :
    chen1973Lemma6Eq19CircleFourthEnvelope Q (σ + v * I) r + 1 ≤
      chen1973Lemma6Eq19SecondCircleFixedPower Q σ r * (1 + v) ^ 8 := by
  let A : ℝ := 1 + |σ| + r
  have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg σ, hr.le]
  have ht : 1 ≤ 1 + v := by linarith
  have hnorm : ‖((σ : ℂ) + v * I)‖ + r ≤ A * (1 + v) := by
    calc
      ‖((σ : ℂ) + v * I)‖ + r ≤ |σ| + v + r := by
        have hn := norm_add_le (σ : ℂ) (v * I)
        have hn' : ‖((σ : ℂ) + v * I)‖ ≤ |σ| + v := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hv] using hn
        linarith
      _ ≤ A * (1 + v) := by dsimp [A]; nlinarith [abs_nonneg σ]
  have harg :
      Real.log ((Q : ℝ) * (1 + (‖((σ : ℂ) + v * I)‖ + r))) ≤
        (Q : ℝ) * A * (1 + v) := by
    have hQ0 : 0 ≤ (Q : ℝ) := by positivity
    have hinside : 1 + (‖((σ : ℂ) + v * I)‖ + r) ≤ A * (1 + v) := by
      have hn := norm_add_le (σ : ℂ) (v * I)
      have hn' : ‖((σ : ℂ) + v * I)‖ ≤ |σ| + v := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hv] using hn
      dsimp [A]
      nlinarith [abs_nonneg σ]
    have hargpos : 0 < (Q : ℝ) * (1 + (‖((σ : ℂ) + v * I)‖ + r)) := by positivity
    calc
      Real.log ((Q : ℝ) * (1 + (‖((σ : ℂ) + v * I)‖ + r))) ≤
          (Q : ℝ) * (1 + (‖((σ : ℂ) + v * I)‖ + r)) := Real.log_le_self hargpos.le
      _ ≤ (Q : ℝ) * (A * (1 + v)) := mul_le_mul_of_nonneg_left hinside hQ0
      _ = (Q : ℝ) * A * (1 + v) := by ring
  have hlog0 : 0 ≤ Real.log ((Q : ℝ) *
      (1 + (‖((σ : ℂ) + v * I)‖ + r))) := by
    apply Real.log_nonneg
    have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    have hinner : (1 : ℝ) ≤ 1 + (‖((σ : ℂ) + v * I)‖ + r) := by
      linarith [norm_nonneg ((σ : ℂ) + v * I), hr]
    exact one_le_mul_of_one_le_of_one_le hQr hinner
  have hmain :
      21000000 * (Q : ℝ) ^ 2 * (‖((σ : ℂ) + v * I)‖ + r) ^ 2 *
          Real.log ((Q : ℝ) * (1 + (‖((σ : ℂ) + v * I)‖ + r))) ^ 4 ≤
        (21000000 * (Q : ℝ) ^ 6 * A ^ 6) * (1 + v) ^ 6 := by
    have hnorm2 := pow_le_pow_left₀ (by positivity : 0 ≤ ‖((σ : ℂ) + v * I)‖ + r)
      hnorm 2
    have hlog4 := pow_le_pow_left₀ hlog0 harg 4
    calc
      _ ≤ 21000000 * (Q : ℝ) ^ 2 * (A * (1 + v)) ^ 2 *
          ((Q : ℝ) * A * (1 + v)) ^ 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnorm2 (by positivity)) hlog4
          (by positivity) (by positivity)
      _ = (21000000 * (Q : ℝ) ^ 6 * A ^ 6) * (1 + v) ^ 6 := by ring
  unfold chen1973Lemma6Eq19CircleFourthEnvelope
    chen1973Lemma6Eq19SecondCircleFixedPower
  dsimp [A] at hmain ⊢

  have ht68 : (1 + v) ^ 6 ≤ (1 + v) ^ 8 := pow_le_pow_right₀ ht (by omega)
  have hc : 0 ≤ 21000000 * (Q : ℝ) ^ 6 * (1 + |σ| + r) ^ 6 := by positivity
  have hcmono := mul_le_mul_of_nonneg_left ht68 hc
  have hone : (1 : ℝ) ≤ (1 + v) ^ 8 := one_le_pow₀ ht
  exact (add_le_add (hmain.trans hcmono) hone).trans_eq (by ring)

/-- Fixed beta-lane coefficient after genuine multiplicative `2,4,4` Hölder.
The `L'` contribution visibly retains the nested fourth-root envelope. -/
def chen1973Lemma6Eq19SecondFixedPower
    (x L level B k m H D Q : ℕ) (σ r : ℝ) : ℝ :=
  Real.sqrt (chen1973Lemma6Eq19FixedPairBound x L level B k m D Q σ) *
    Real.sqrt
      (Real.sqrt
          (chen1973Lemma6Eq19I x L level * (Q : ℝ) *
            ((Real.sqrt (Real.sqrt
              (chen1973Lemma6Eq19SecondCircleFixedPower Q σ r)) / r) ^ 4)) *
        Real.sqrt
          (chen1973Lemma6Eq19I x L level *
            (chen1973Lemma6Eq19SharpConstant *
              ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
              (1 + Real.log (H * H : ℕ)) ^ 4)))

/-- The beta numerator has a derived quadratic envelope.  Its proof uses the
literal multiplicative `2,4,4` Hölder theorem and the sharp fourth-root Cauchy
bound, rather than a postulated growth hypothesis. -/
theorem chen1973Lemma6_eq19_second_le_fixedPower
    (x L level B k m H D Q : ℕ) (σ r v : ℝ)
    (hD : 0 < D) (hQ : 2 ≤ Q) (hr : 0 < r) (hv : 0 ≤ v)
    (hcellIoc : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q)
    (hcellIcc : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q)
    (hdom : ∀ t ∈ Set.Icc (-v) v,
      Chen1973Lemma3Domain (σ + t * I) σ t)
    (hsphere : ∀ z ∈ Metric.sphere (σ + v * I) r,
      Chen1973Lemma3Domain z z.re z.im) :
    chen1973Lemma6B x L level B k m H (σ + v * I) ≤
      chen1973Lemma6Eq19SecondFixedPower x L level B k m H D Q σ r *
        (1 + v) ^ 2 := by
  let P := chen1973Lemma6Eq19FixedPairBound x L level B k m D Q σ
  let K := chen1973Lemma6Eq19SecondCircleFixedPower Q σ r
  let J := chen1973Lemma6Eq19I x L level * (Q : ℝ)
  let M := chen1973Lemma6Eq19I x L level *
    (chen1973Lemma6Eq19SharpConstant *
      ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
      (1 + Real.log (H * H : ℕ)) ^ 4)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hP : 0 ≤ P := by
    dsimp [P, chen1973Lemma6Eq19FixedPairBound]
    exact mul_nonneg (chen1973Lemma6Eq19I_pos x L level).le
      (mul_nonneg
        (mul_nonneg chen1973Lemma6_eq19SharpConstant_pos.le
          (add_nonneg (by positivity) (div_nonneg (by positivity) hDR.le)))
        (Finset.sum_nonneg fun pp hpp => by positivity))
  have hK : 0 ≤ K := by dsimp [K, chen1973Lemma6Eq19SecondCircleFixedPower]; positivity
  have hJ : 0 ≤ J := mul_nonneg (chen1973Lemma6Eq19I_pos x L level).le (by positivity)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (chen1973Lemma6Eq19I_pos x L level).le
      (mul_nonneg (mul_nonneg chen1973Lemma6_eq19SharpConstant_pos.le
        (add_nonneg (by positivity) (div_nonneg (by positivity) hDR.le))) (by positivity))
  have ht : 0 ≤ 1 + v := by linarith
  have hp := chen1973Lemma6_eq19_pair_second_moment_fixed_height
    x L level B k m D Q σ v hD hcellIoc
  have hL0 := chen1973Lemma6_eq19_LDeriv_fourth_moment_sharp_cauchy
    x L level Q (σ + v * I) r hQ hr hcellIcc hsphere
  have hcircle := eq19_circleEnvelope_le_fixedPower Q σ r v hQ hr hv
  have hroot := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hcircle)
  have hrootmul :
      Real.sqrt (Real.sqrt
        (chen1973Lemma6Eq19CircleFourthEnvelope Q (σ + v * I) r + 1)) ≤
        Real.sqrt (Real.sqrt K) * (1 + v) ^ 2 := by
    have ht4 : Real.sqrt ((1 + v) ^ 8) = (1 + v) ^ 4 := by
      rw [show (1 + v) ^ 8 = ((1 + v) ^ 4) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have ht2 : Real.sqrt ((1 + v) ^ 4) = (1 + v) ^ 2 := by
      rw [show (1 + v) ^ 4 = ((1 + v) ^ 2) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    rw [Real.sqrt_mul hK, ht4, Real.sqrt_mul (Real.sqrt_nonneg K), ht2] at hroot
    simpa [K] using hroot
  have hL : chen1973Lemma6Eq19LDerivFourthMoment x L level (σ + v * I) ≤
      J * ((Real.sqrt (Real.sqrt K) / r) ^ 4) * (1 + v) ^ 8 := by
    refine hL0.trans ?_
    dsimp [J]
    have hdiv := div_le_div_of_nonneg_right hrootmul hr.le
    have hpw := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) hr.le) hdiv 4
    calc
      _ ≤ chen1973Lemma6Eq19I x L level * (Q : ℝ) *
          (((Real.sqrt (Real.sqrt K) / r) * (1 + v) ^ 2) ^ 4) := by
            apply mul_le_mul_of_nonneg_left
            · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpw
            · positivity
      _ = J * ((Real.sqrt (Real.sqrt K) / r) ^ 4) * (1 + v) ^ 8 := by
        dsimp [J]
        ring
  have hMob := chen1973Lemma6_eq19_mobius_fourth_moment_uniform
    x L level H D Q σ v hD hcellIoc
      hdom
      v (by constructor <;> linarith)
  have hbase := chen1973Lemma6B_le_moment_product x L level B k m H (σ + v * I)
  unfold chen1973Lemma6Eq19SecondFixedPower
  change _ ≤ Real.sqrt P *
      Real.sqrt (Real.sqrt (J * (Real.sqrt (Real.sqrt K) / r) ^ 4) * Real.sqrt M) *
        (1 + v) ^ 2
  refine hbase.trans ?_
  have hsL := Real.sqrt_le_sqrt hL
  have hsM := Real.sqrt_le_sqrt hMob
  have hsL' : Real.sqrt (chen1973Lemma6Eq19LDerivFourthMoment x L level (σ + v * I)) ≤
      Real.sqrt (J * (Real.sqrt (Real.sqrt K) / r) ^ 4) * (1 + v) ^ 4 := by
    have ht4 : Real.sqrt ((1 + v) ^ 8) = (1 + v) ^ 4 := by
      rw [show (1 + v) ^ 8 = ((1 + v) ^ 4) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    rw [Real.sqrt_mul (mul_nonneg hJ (by positivity)), ht4] at hsL
    exact hsL
  calc
    _ ≤ Real.sqrt P *
        Real.sqrt
          ((Real.sqrt (J * (Real.sqrt (Real.sqrt K) / r) ^ 4) * (1 + v) ^ 4) *
            Real.sqrt M) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hp)
        (Real.sqrt_le_sqrt (mul_le_mul hsL' hsM (Real.sqrt_nonneg _) (by positivity)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt P *
        Real.sqrt (Real.sqrt (J * (Real.sqrt (Real.sqrt K) / r) ^ 4) * Real.sqrt M) *
          (1 + v) ^ 2 := by
      rw [show Real.sqrt (J * (Real.sqrt (Real.sqrt K) / r) ^ 4) *
          (1 + v) ^ 4 * Real.sqrt M =
          (Real.sqrt (J * (Real.sqrt (Real.sqrt K) / r) ^ 4) * Real.sqrt M) *
            (1 + v) ^ 4 by ring,
        Real.sqrt_mul (by positivity : 0 ≤
          Real.sqrt (J * (Real.sqrt (Real.sqrt K) / r) ^ 4) * Real.sqrt M),
        show Real.sqrt ((1 + v) ^ 4) = (1 + v) ^ 2 by
          rw [show (1 + v) ^ 4 = ((1 + v) ^ 2) ^ 2 by ring,
            Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]]
      ring

/-- The beta fixed-power profile is integrable on the positive half-line. -/
theorem chen1973Lemma6_eq19_quadraticDecay_integrable :
    IntegrableOn chen1973Lemma6Eq19QuadraticDecay (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · apply (show Continuous chen1973Lemma6Eq19QuadraticDecay by
      unfold chen1973Lemma6Eq19QuadraticDecay
      refine Continuous.div ((continuous_const.add continuous_id).pow 2)
        (continuous_const.add (continuous_abs.pow 4)) ?_
      intro v
      positivity).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set
    exact Ioc_subset_Icc_self
  · have hpow : IntegrableOn (fun v : ℝ => 4 * v ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 4
    apply Integrable.mono' hpow
    · exact (show Continuous chen1973Lemma6Eq19QuadraticDecay by
        unfold chen1973Lemma6Eq19QuadraticDecay
        refine Continuous.div ((continuous_const.add continuous_id).pow 2)
          (continuous_const.add (continuous_abs.pow 4)) ?_
        intro v
        positivity).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := zero_lt_one.trans hv
      have hv1 : 1 ≤ v := hv.le
      have hnum : (1 + v) ^ 2 ≤ 4 * v ^ 2 := by nlinarith [sq_nonneg (v - 1)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        unfold chen1973Lemma6Eq19QuadraticDecay; positivity),
        chen1973Lemma6Eq19QuadraticDecay, abs_of_pos hv0]
      calc
        (1 + v) ^ (2 : ℕ) / (1 + v ^ (4 : ℕ)) ≤
            (4 * v ^ 2) / v ^ 4 := by
          exact div_le_div₀ (by positivity) hnum (by positivity) (by linarith)
        _ = 4 * v ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast v 2, ← Real.rpow_natCast v 4,
            div_eq_mul_inv, ← Real.rpow_neg hv0.le]
          calc
            4 * v ^ (2 : ℝ) * v ^ (-(4 : ℝ)) =
                4 * (v ^ (2 : ℝ) * v ^ (-(4 : ℝ))) := by ring
            _ = 4 * v ^ ((2 : ℝ) + (-(4 : ℝ))) := by
              rw [← Real.rpow_add hv0]
            _ = 4 * v ^ (-2 : ℝ) := by norm_num

private theorem eq19_corrected_inv_le_fourth
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ)
    (horder : 4 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
      (2 * Real.log x ^ ((22 : ℝ) / 5) / σ) /
        (1 + |v| ^ (4 : ℝ)) := by
  have hfac := chen1973Lemma6_eq17_correctedFactor_vertical_inv_le_fourth_power
    hx σ v horder
  have hnorm : σ ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    calc
      σ = |((σ : ℂ) + (v : ℂ) * I).re| := by simp [abs_of_pos hσ]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hcalc :
      ‖((σ : ℂ) + (v : ℂ) * I)‖⁻¹ *
          (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
            chen1973PerronScale (x : ℝ)) ^
              (chen1973PerronOrder (x : ℝ) + 1))⁻¹ ≤
      σ⁻¹ * (2 * Real.log x ^ ((22 : ℝ) / 5) / (1 + |v| ^ (4 : ℕ))) := by
    have hfac0 : 0 ≤
        (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
          chen1973PerronScale (x : ℝ)) ^
            (chen1973PerronOrder (x : ℝ) + 1))⁻¹ := by
      apply inv_nonneg.mpr
      have hscale : 0 < chen1973PerronScale (x : ℝ) :=
        chen1973Lemma6_eq17_perronScale_pos (by omega)
      linarith [pow_nonneg
        (div_nonneg (norm_nonneg ((σ : ℂ) + (v : ℂ) * I)) hscale.le)
        (chen1973PerronOrder (x : ℝ) + 1)]
    exact mul_le_mul (inv_anti₀ hσ hnorm) hfac hfac0 (inv_nonneg.mpr hσ.le)
  simpa [chen1973Lemma6Eq17CorrectedKernel, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc, Real.rpow_natCast] using hcalc

/-- Explicit beta-envelope integral and bound, with neither a caller-supplied
growth hypothesis nor a continuity hypothesis. -/
theorem chen1973Lemma6_eq19_second_fixedPower_integrable_and_bound
    (x L level B k m H D Q : ℕ) (σ r : ℝ)
    (hx : 3 ≤ x) (hσ : 0 < σ)
    (horder : 4 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    let F := fun v : ℝ =>
      chen1973Lemma6Eq19SecondFixedPower x L level B k m H D Q σ r *
          (1 + v) ^ 2 /
        chen1973Lemma6Eq17CorrectedKernel x (σ + v * I)
    IntegrableOn F (Ioi 0) ∧
      (∫ v in Ioi (0 : ℝ), F v) ≤
        (2 * Real.log x ^ ((22 : ℝ) / 5) / σ) *
          chen1973Lemma6Eq19SecondFixedPower x L level B k m H D Q σ r *
          ∫ v in Ioi (0 : ℝ), chen1973Lemma6Eq19QuadraticDecay v := by
  dsimp
  let G := chen1973Lemma6Eq19SecondFixedPower x L level B k m H D Q σ r
  have hG : 0 ≤ G := by dsimp [G, chen1973Lemma6Eq19SecondFixedPower]; positivity
  let C := 2 * Real.log x ^ ((22 : ℝ) / 5) / σ
  have hmajor : IntegrableOn (fun v => C * G * chen1973Lemma6Eq19QuadraticDecay v)
      (Ioi 0) := chen1973Lemma6_eq19_quadraticDecay_integrable.const_mul (C * G)
  have hint : IntegrableOn (fun v : ℝ =>
      G * (1 + v) ^ 2 / chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))
      (Ioi 0) := by
    apply Integrable.mono' hmajor
    · apply Continuous.aestronglyMeasurable
      apply Continuous.div
      · fun_prop
      · unfold chen1973Lemma6Eq17CorrectedKernel
        fun_prop
      · intro v
        exact (chen1973Lemma6_eq17_correctedKernel_pos (by omega : 1 < x) hσ).ne'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hk := chen1973Lemma6_eq17_correctedKernel_pos
        (x := x) (v := v) (by omega : 1 < x) hσ
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hG (by positivity)) hk.le),
        div_eq_mul_inv]
      have hi := eq19_corrected_inv_le_fourth hx (v := v) hσ horder
      calc
        G * (1 + v) ^ 2 * (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
            G * (1 + v) ^ 2 * (C / (1 + |v| ^ (4 : ℕ))) :=
          mul_le_mul_of_nonneg_left (by simpa [C, Real.rpow_natCast] using hi) (by positivity)
        _ = C * G * chen1973Lemma6Eq19QuadraticDecay v := by
          unfold chen1973Lemma6Eq19QuadraticDecay
          ring
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ v in Ioi (0 : ℝ), C * G * chen1973Lemma6Eq19QuadraticDecay v := by
      apply integral_mono_ae hint hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [div_eq_mul_inv]
      have hi := eq19_corrected_inv_le_fourth hx (v := v) hσ horder
      exact (mul_le_mul_of_nonneg_left (by simpa [C] using hi) (by positivity)).trans_eq (by
        unfold chen1973Lemma6Eq19QuadraticDecay; ring)
    _ = C * G * ∫ v in Ioi (0 : ℝ), chen1973Lemma6Eq19QuadraticDecay v := by
      rw [MeasureTheory.integral_const_mul]

end AnalyticNumberTheory.LargeSieve
