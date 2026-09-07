import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovVanishing
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Integer parameters for the Stepanov construction

Harcos, *Weil's bound for Kloosterman sums*, printed
page 12 (`pages/harcos-weil-12.png`). The coefficient spaces have integer
dimension `2 * J * B`; the equation space has the actual dimension
`∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1))`.
The ceiling choices below prove the strict inequality between these dimensions.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

/-- The multiplicity parameter on Harcos's printed page 12. -/
def stepanovEll (q : ℕ) : ℕ := ⌈Real.sqrt (q : ℝ)⌉₊

/-- The integer number of coefficients in each polynomial block. -/
def stepanovB (q m : ℕ) : ℕ := ⌈((q : ℝ) - m) / 2⌉₊

/-- The integer number of blocks in each of the two polynomial families. -/
def stepanovJ (q m ell : ℕ) : ℕ :=
  ⌈(ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q⌉₊

/-- Exact equation count, not an estimate for a hypothetical system. -/
theorem stepanov_equation_count (ell B J m : ℕ) :
    (∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1))) =
      ell * (B + (J - 1)) + (ell * (ell - 1) / 2) * (m - 1) := by
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k) ell, Finset.sum_range_id]
  ring

/-- The real form of the exact count, with no rounding of dimensions. -/
theorem stepanov_equation_count_real (ell B J m : ℕ)
    (hell : 0 < ell) (hJ : 0 < J) (hm : 1 ≤ m) :
    ((∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) : ℕ) : ℝ) =
      (ell : ℝ) * (B + J - 1) +
        (ell : ℝ) * (ell - 1) / 2 * (m - 1) := by
  have hsum : (∑ k : Fin ell, (k.val : ℝ)) * 2 =
      (ell : ℝ) * (ell - 1) := by
    have h := Finset.sum_range_id_mul_two ell
    rw [← Fin.sum_univ_eq_sum_range] at h
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hell)), Nat.cast_one] using h'
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hJ)),
    Nat.cast_sub hm]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-- For `q > 18`, the source's ceiling of the square root satisfies both
the construction's range restriction and the final square-root bound. -/
theorem stepanovEll_bounds {q : ℕ} (hq : 18 < q) :
    0 < stepanovEll q ∧ 3 * stepanovEll q ≤ q ∧ q ≤ stepanovEll q ^ 2 := by
  have hqR : (19 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hs2 := Real.sq_sqrt hq0
  have helo := Nat.le_ceil (Real.sqrt (q : ℝ))
  have hehi := Nat.ceil_lt_add_one hs0
  have hsbound : Real.sqrt (q : ℝ) + 1 ≤ (q : ℝ) / 3 := by
    have hsq : (q : ℝ) ≤ ((q : ℝ) / 3 - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqR) hq0]
    nlinarith
  have helpos : 0 < stepanovEll q := by
    apply Nat.ceil_pos.mpr
    positivity
  refine ⟨helpos, ?_, ?_⟩
  · have : (3 : ℝ) * stepanovEll q ≤ q := by
      dsimp [stepanovEll]
      linarith
    exact_mod_cast this
  · have : (q : ℝ) ≤ (stepanovEll q : ℝ) ^ 2 := by
      dsimp [stepanovEll]
      nlinarith
    exact_mod_cast this

/-- The ceiling defining the coefficient-block size respects the strict
nonvanishing restriction `2(B-1)+m < q`. -/
theorem stepanovB_bounds {q m : ℕ} (hmq : m < q) :
    0 < stepanovB q m ∧
      ((q : ℝ) - m) / 2 ≤ stepanovB q m ∧
      (stepanovB q m : ℝ) < ((q : ℝ) - m) / 2 + 1 ∧
      2 * (stepanovB q m - 1) + m < q := by
  have hmqR : (m : ℝ) < q := by exact_mod_cast hmq
  have ht : 0 < ((q : ℝ) - m) / 2 := by linarith
  have hpos : 0 < stepanovB q m := Nat.ceil_pos.mpr ht
  have hlo := Nat.le_ceil (((q : ℝ) - m) / 2)
  have hhi := Nat.ceil_lt_add_one (le_of_lt ht)
  refine ⟨hpos, hlo, hhi, ?_⟩
  have hcast : ((stepanovB q m - 1 : ℕ) : ℝ) = stepanovB q m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)), Nat.cast_one]
  have : (2 : ℝ) * ((stepanovB q m - 1 : ℕ) : ℝ) + m < q := by
    rw [hcast]
    dsimp [stepanovB]
    linarith
  exact_mod_cast this

/-- Integer rounding of the two block parameters gives strictly more
unknown coefficients than actual coefficient equations. -/
theorem stepanov_parameters_count {q m ell : ℕ}
    (hm : 3 ≤ m) (hmq : 6 * m < q)
    (hell : 0 < ell) (hellq : 3 * ell ≤ q) :
    0 < stepanovJ q m ell ∧
      (∑ k : Fin ell,
        (stepanovB q m + k.val * (m - 1) + (stepanovJ q m ell - 1))) <
        2 * stepanovJ q m ell * stepanovB q m := by
  let B := stepanovB q m
  let J := stepanovJ q m ell
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmqR : (6 : ℝ) * m < q := by exact_mod_cast hmq
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hellqR : (3 : ℝ) * ell ≤ q := by exact_mod_cast hellq
  have hu : 0 < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q := by positivity
  have hJ : 0 < J := Nat.ceil_pos.mpr hu
  have hJlo : (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q ≤ J :=
    Nat.le_ceil _
  obtain ⟨_, hBlo, hBhi, _⟩ := stepanovB_bounds (show m < q by omega)
  change ((q : ℝ) - m) / 2 ≤ (B : ℝ) at hBlo
  change (B : ℝ) < ((q : ℝ) - m) / 2 + 1 at hBhi
  have hJshift : 0 ≤ (J : ℝ) - (ell : ℝ) / 2 := by
    have : 0 ≤ (ell : ℝ) ^ 2 * m / q := by positivity
    linarith
  have hhalf : (q : ℝ) / 2 ≤ q - m - ell := by linarith
  have hshiftq : (ell : ℝ) ^ 2 * m ≤ ((J : ℝ) - (ell : ℝ) / 2) * q :=
    (div_le_iff₀ hq).mp (by linarith)
  have hshift := mul_le_mul_of_nonneg_left hhalf hJshift
  have hdimension :
      (ell : ℝ) * (((q : ℝ) - m) / 2 + J) +
        (ell : ℝ) ^ 2 / 2 * (m - 1) ≤ (J : ℝ) * (q - m) := by
    nlinarith only [hshiftq, hshift]
  have hcountReal := stepanov_equation_count_real ell B J m hell hJ (by omega)
  have hupper :
      ((∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) : ℕ) : ℝ) <
        (ell : ℝ) * (((q : ℝ) - m) / 2 + J) +
          (ell : ℝ) ^ 2 / 2 * (m - 1) := by
    have hmul := mul_lt_mul_of_pos_left hBhi hellR
    have hpay : 0 ≤ (ell : ℝ) * (m - 1) :=
      mul_nonneg (le_of_lt hellR) (by linarith)
    nlinarith only [hcountReal, hmul, hpay]
  have hlower : (J : ℝ) * (q - m) ≤ 2 * J * B := by
    have hmul := mul_le_mul_of_nonneg_left hBlo (show 0 ≤ (2 : ℝ) * J by positivity)
    nlinarith only [hmul]
  refine ⟨hJ, ?_⟩
  have := hupper.trans_le (hdimension.trans hlower)
  exact_mod_cast this

/-- The same rounded parameters meet the source's degree budget.
Only the final step uses `q ≤ ell²`; no parity assumption is needed here. -/
theorem stepanov_parameters_degree {q m ell : ℕ}
    (hm : 3 ≤ m) (hmq : 6 * m < q)
    (hell : 0 < ell) (hellq : 3 * ell ≤ q) (hqsq : q ≤ ell ^ 2) :
    ((stepanovB q m + (q - 1) / 2 * m + (stepanovJ q m ell - 1) * q +
      ell * m : ℕ) : ℝ) <
      (ell : ℝ) * ((q : ℝ) / 2 + 2 * m * ell) := by
  let B := stepanovB q m
  let J := stepanovJ q m ell
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hellqR : (3 : ℝ) * ell ≤ q := by exact_mod_cast hellq
  have hqsqR : (q : ℝ) ≤ (ell : ℝ) ^ 2 := by exact_mod_cast hqsq
  have hu : 0 < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q := by positivity
  have hJ : 0 < J := Nat.ceil_pos.mpr hu
  have hJhi : (J : ℝ) < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q + 1 :=
    Nat.ceil_lt_add_one (le_of_lt hu)
  have hBhi : (B : ℝ) < ((q : ℝ) - m) / 2 + 1 :=
    (stepanovB_bounds (show m < q by omega)).2.2.1
  have hJmul : ((J : ℝ) - 1) * q <
      (ell : ℝ) / 2 * q + (ell : ℝ) ^ 2 * m := by
    have h := (lt_div_iff₀ hq).mp
      (show (J : ℝ) - 1 - (ell : ℝ) / 2 < (ell : ℝ) ^ 2 * m / q by linarith)
    nlinarith only [h]
  have hhalf : (2 : ℝ) * (((q - 1) / 2 : ℕ) : ℝ) ≤ q := by
    exact_mod_cast (show 2 * ((q - 1) / 2) ≤ q by omega)
  have hhalfM := mul_le_mul_of_nonneg_right hhalf (show (0 : ℝ) ≤ m by positivity)
  have hellM := mul_le_mul_of_nonneg_right hellqR (show (0 : ℝ) ≤ m by positivity)
  have hmqnonneg : 0 ≤ (q : ℝ) * (m - 3) := by positivity
  have hD :
      ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) =
        (B : ℝ) + (((q - 1) / 2 : ℕ) : ℝ) * m +
          ((J : ℝ) - 1) * q + (ell : ℝ) * m := by
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hJ))]
    rfl
  have hbudget :
      ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) <
        (m : ℝ) * q + (ell : ℝ) * q / 2 + (ell : ℝ) ^ 2 * m := by
    nlinarith only [hD, hBhi, hJmul, hhalfM, hellM, hmqnonneg, hmR]
  have hsqM := mul_le_mul_of_nonneg_right hqsqR (show (0 : ℝ) ≤ m by positivity)
  change ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) < _
  nlinarith only [hbudget, hsqM]

/-- All numerical requirements for the genuine finite-dimensional construction,
including its exact equation count and a strict real degree budget. -/
structure StepanovParameterBounds (q m ell B J : ℕ) : Prop where
  ell_pos : 0 < ell
  ell_le_card : ell ≤ q
  three_mul_ell_le : 3 * ell ≤ q
  card_le_ell_sq : q ≤ ell ^ 2
  B_pos : 0 < B
  J_pos : 0 < J
  coefficient_bound : 2 * (B - 1) + m < q
  equation_count_lt :
    (∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1))) < 2 * J * B
  degree_budget :
    ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) <
      (ell : ℝ) * ((q : ℝ) / 2 + 2 * m * ell)

/-- Harcos's three ceiling choices satisfy every integer constraint.
This numerical theorem is valid even without assuming `q` odd. -/
theorem stepanov_integer_parameters (q m : ℕ) (hm : 3 ≤ m) (hmq : 6 * m < q) :
    StepanovParameterBounds q m (stepanovEll q) (stepanovB q m)
      (stepanovJ q m (stepanovEll q)) := by
  obtain ⟨hell, hellq, hqsq⟩ := stepanovEll_bounds (show 18 < q by omega)
  obtain ⟨hB, _, _, hBq⟩ := stepanovB_bounds (show m < q by omega)
  obtain ⟨hJ, hcount⟩ := stepanov_parameters_count hm hmq hell hellq
  exact ⟨hell, by omega, hellq, hqsq, hB, hJ, hBq, hcount,
    stepanov_parameters_degree hm hmq hell hellq hqsq⟩

/-- An existential interface spelling out the source-matching choices. -/
theorem stepanov_integer_parameters_exists (q m : ℕ)
    (hm : 3 ≤ m) (hmq : 6 * m < q) :
    ∃ ell B J : ℕ,
      ell = ⌈Real.sqrt (q : ℝ)⌉₊ ∧
      B = ⌈((q : ℝ) - m) / 2⌉₊ ∧
      J = ⌈(ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q⌉₊ ∧
      StepanovParameterBounds q m ell B J :=
  ⟨stepanovEll q, stepanovB q m, stepanovJ q m (stepanovEll q),
    rfl, rfl, rfl, stepanov_integer_parameters q m hm hmq⟩

/-- The actual auxiliary polynomial with no assumed dimension inequality:
the integer choices above discharge all numerical construction hypotheses.
Both the strict integer degree bound and its real budget are retained. -/
theorem stepanov_exists_auxiliary_polynomial_of_large_card
    {F : Type*} [Field F] [Fintype F] (f : F[X]) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    let q := Fintype.card F
    let ell := stepanovEll q
    let B := stepanovB q f.natDegree
    let J := stepanovJ q f.natDegree ell
    ∃ h : F[X], h ≠ 0 ∧
      h.degree < ((B + (q - 1) / 2 * f.natDegree +
        (J - 1) * q + ell * f.natDegree : ℕ) : WithBot ℕ) ∧
      (h.natDegree : ℝ) < (ell : ℝ) * ((q : ℝ) / 2 + 2 * f.natDegree * ell) ∧
      ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((q - 1) / 2) = a →
        ∀ k < ell, (hasseDeriv k h).eval x = 0 := by
  dsimp only
  have hp := stepanov_integer_parameters (Fintype.card F) f.natDegree hm hmq
  obtain ⟨h, hnz, hdeg, hvan⟩ := stepanov_exists_auxiliary_polynomial f
    (stepanovEll (Fintype.card F)) (stepanovB (Fintype.card F) f.natDegree)
    (stepanovJ (Fintype.card F) f.natDegree (stepanovEll (Fintype.card F)))
    a hq hf0 hf (by omega) hp.J_pos hp.ell_le_card hp.coefficient_bound
    hp.equation_count_lt
  refine ⟨h, hnz, hdeg, ?_, hvan⟩
  have hnat := (natDegree_lt_iff_degree_lt hnz).mpr hdeg
  have hreal :
      (h.natDegree : ℝ) <
        ((stepanovB (Fintype.card F) f.natDegree +
          (Fintype.card F - 1) / 2 * f.natDegree +
          (stepanovJ (Fintype.card F) f.natDegree (stepanovEll (Fintype.card F)) - 1) *
            Fintype.card F + stepanovEll (Fintype.card F) * f.natDegree : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hp.degree_budget

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
