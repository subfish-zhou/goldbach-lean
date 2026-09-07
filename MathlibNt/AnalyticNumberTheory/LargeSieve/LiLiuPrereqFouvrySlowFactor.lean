import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# The concrete five-variable slow factor, in logarithmic coordinates

The coordinate order is `(h,k,n,r,s)`. Logarithmic coordinates are convenient
for dyadic partial summation: their interval lengths are at most `log 2`,
independently of the original arithmetic scales. The two real phase parameters
include all scaling constants; arithmetic coefficients and reciprocal/root
phases are not part of this weight.
-/

noncomputable section

open scoped BigOperators

namespace LiLiuPrereqFouvry.SlowFactor

abbrev Point := Fin 5 → ℝ

def linear (m x : Point) : ℝ := ∑ i, m i * x i

def phaseA : Point := ![1, -1, 0, -1, -1]
def phaseB : Point := ![1, -1, -1, -1, -1]
def amplitude : Point := ![0, -1, 0, -1, -1]

def atom (A B : ℝ) (m x : Point) : ℂ :=
  Complex.exp ((linear m x : ℂ) + Complex.I * (2 * Real.pi) *
    (A * Real.exp (linear phaseA x) + B * Real.exp (linear phaseB x)))

def weight (A B : ℝ) : Point → ℂ := atom A B amplitude

def coeffA (A : ℝ) (j : Fin 5) : ℂ :=
  Complex.I * (2 * Real.pi) * A * phaseA j

def coeffB (B : ℝ) (j : Fin 5) : ℂ :=
  Complex.I * (2 * Real.pi) * B * phaseB j

theorem linear_add (m p x : Point) :
    linear (m + p) x = linear m x + linear p x := by
  simp [linear, add_mul, Finset.sum_add_distrib]

theorem linear_update (m x : Point) (j : Fin 5) (t : ℝ) :
    linear m (Function.update x j t) = linear m x + m j * (t - x j) := by
  classical
  rw [linear, linear, ← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have heq : (∑ i ∈ Finset.univ.erase j, m i * Function.update x j t i) =
      ∑ i ∈ Finset.univ.erase j, m i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [heq, Function.update_self]
  ring

theorem hasDerivAt_linear (m x : Point) (j : Fin 5) :
    HasDerivAt (fun t => linear m (Function.update x j t)) (m j) (x j) := by
  simp_rw [linear_update]
  simpa using (((hasDerivAt_id (x j)).sub_const (x j)).const_mul (m j)).const_add
    (linear m x)

theorem atom_shift (A B : ℝ) (m p x : Point) :
    atom A B (m + p) x = atom A B m x * (Real.exp (linear p x) : ℂ) := by
  unfold atom
  simp only [linear_add, Complex.ofReal_add, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem norm_atom (A B : ℝ) (m x : Point) :
    ‖atom A B m x‖ = Real.exp (linear m x) := by
  simp [atom, Complex.norm_exp, Complex.add_re, Complex.mul_re, Complex.mul_im]

theorem hasDerivAt_atom (A B : ℝ) (m x : Point) (j : Fin 5) :
    HasDerivAt (fun t => atom A B m (Function.update x j t))
      ((m j : ℂ) * atom A B m x +
        coeffA A j * atom A B (m + phaseA) x +
        coeffB B j * atom A B (m + phaseB) x) (x j) := by
  have hm := (hasDerivAt_linear m x j).ofReal_comp
  have ha := ((hasDerivAt_linear phaseA x j).exp.const_mul A).ofReal_comp
  have hb := ((hasDerivAt_linear phaseB x j).exp.const_mul B).ofReal_comp
  have hh := (hm.add ((ha.add hb).const_mul (Complex.I * (2 * Real.pi)))).cexp
  simp only [Pi.add_apply, Function.update_eq_self] at hh
  convert hh using 1
  · ext t
    simp only [atom, Complex.ofReal_mul]
  · rw [atom_shift, atom_shift]
    simp only [atom, coeffA, coeffB, Complex.ofReal_mul]
    ring

/-- Appending an index differentiates once in that coordinate; see
`hasDerivAt_jet`. Repeated indices are allowed, so this covers more than the
32 mixed derivatives with each coordinate used at most once. -/
def jet (A B : ℝ) : List (Fin 5) → Point → Point → ℂ
  | [], m, x => atom A B m x
  | j :: js, m, x =>
      (m j : ℂ) * jet A B js m x +
      coeffA A j * jet A B js (m + phaseA) x +
      coeffB B j * jet A B js (m + phaseB) x

theorem hasDerivAt_jet (A B : ℝ) (js : List (Fin 5)) (m x : Point)
    (j : Fin 5) :
    HasDerivAt (fun t => jet A B js m (Function.update x j t))
      (jet A B (js ++ [j]) m x) (x j) := by
  induction js generalizing m with
  | nil => simpa [jet] using hasDerivAt_atom A B m x j
  | cons i js ih =>
    convert
      (((ih m).const_mul (m i : ℂ)).add
        ((ih (m + phaseA)).const_mul (coeffA A i))).add
          ((ih (m + phaseB)).const_mul (coeffB B i)) using 1
    all_goals rfl

theorem jet_append_eq_deriv (A B : ℝ) (js : List (Fin 5)) (m x : Point)
    (j : Fin 5) :
    jet A B (js ++ [j]) m x =
      deriv (fun t => jet A B js m (Function.update x j t)) (x j) :=
  (hasDerivAt_jet A B js m x j).deriv.symm

def logBox (x : Point) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i ≤ Real.log 2

theorem phaseA_abs_le (j : Fin 5) : |phaseA j| ≤ 1 := by
  revert j
  norm_num [Fin.forall_fin_succ, phaseA]

theorem phaseB_abs_le (j : Fin 5) : |phaseB j| ≤ 1 := by
  revert j
  norm_num [Fin.forall_fin_succ, phaseB]

theorem linear_phaseA_le {x : Point} (hx : logBox x) :
    linear phaseA x ≤ Real.log 2 := by
  have h0 := (hx 0).2
  have h1 := (hx 1).1
  have h3 := (hx 3).1
  have h4 := (hx 4).1
  simp [linear, phaseA, Fin.sum_univ_succ]
  linarith

theorem linear_phaseB_le {x : Point} (hx : logBox x) :
    linear phaseB x ≤ Real.log 2 := by
  have h0 := (hx 0).2
  have h1 := (hx 1).1
  have h2 := (hx 2).1
  have h3 := (hx 3).1
  have h4 := (hx 4).1
  simp [linear, phaseB, Fin.sum_univ_succ]
  linarith

theorem norm_coeffA_le (A : ℝ) (j : Fin 5) :
    ‖coeffA A j‖ ≤ 2 * Real.pi * |A| := by
  calc
    ‖coeffA A j‖ = (2 * Real.pi * |A|) * |phaseA j| := by
      simp [coeffA, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    _ ≤ (2 * Real.pi * |A|) * 1 :=
      mul_le_mul_of_nonneg_left (phaseA_abs_le j) (by positivity)
    _ = _ := mul_one _

theorem norm_coeffB_le (B : ℝ) (j : Fin 5) :
    ‖coeffB B j‖ ≤ 2 * Real.pi * |B| := by
  calc
    ‖coeffB B j‖ = (2 * Real.pi * |B|) * |phaseB j| := by
      simp [coeffB, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    _ ≤ (2 * Real.pi * |B|) * 1 :=
      mul_le_mul_of_nonneg_left (phaseB_abs_le j) (by positivity)
    _ = _ := mul_one _

/-- A quantitative estimate for every concrete mixed derivative of every
exponential monomial generated by the derivative recurrence. No derivative
bound is a hypothesis: the assumptions concern only the initial linear
exponent and the two real phase parameters. -/
theorem norm_jet_le (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (js : List (Fin 5)) (m x : Point) (hx : logBox x) (R : ℕ)
    (hm : ∀ j, |m j| ≤ R)
    (hl : linear m x ≤ R * Real.log 2) :
    ‖jet A B js m x‖ ≤
      (2 : ℝ) ^ (R + js.length) *
        ((R + js.length : ℕ) + 2 * Real.pi * V) ^ js.length := by
  have hV0 : 0 ≤ V := le_trans (by positivity : 0 ≤ |A| + |B|) hV
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  induction js generalizing m R with
  | nil =>
    simp only [jet, norm_atom, List.length_nil, Nat.add_zero, pow_zero, mul_one]
    calc
      Real.exp (linear m x) ≤ Real.exp (R * Real.log 2) := Real.exp_le_exp.mpr hl
      _ = (2 : ℝ) ^ R := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  | cons j js ih =>
    let T : ℝ := (R + 1 + js.length : ℕ) + 2 * Real.pi * V
    let K : ℝ := (2 : ℝ) ^ (R + 1 + js.length) * T ^ js.length
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hr : (R : ℝ) ≤ R + 1 := by linarith
    have hm0 : ∀ i, |m i| ≤ (R + 1 : ℕ) := by
      intro i
      exact (hm i).trans (by exact_mod_cast Nat.le_succ R)
    have hl0 : linear m x ≤ (R + 1 : ℕ) * Real.log 2 := by
      push_cast
      nlinarith
    have hmA : ∀ i, |(m + phaseA) i| ≤ (R + 1 : ℕ) := by
      intro i
      simpa only [Pi.add_apply, Nat.cast_add, Nat.cast_one] using
        (abs_add_le (m i) (phaseA i)).trans (add_le_add (hm i) (phaseA_abs_le i))
    have hmB : ∀ i, |(m + phaseB) i| ≤ (R + 1 : ℕ) := by
      intro i
      simpa only [Pi.add_apply, Nat.cast_add, Nat.cast_one] using
        (abs_add_le (m i) (phaseB i)).trans (add_le_add (hm i) (phaseB_abs_le i))
    have hlA : linear (m + phaseA) x ≤ (R + 1 : ℕ) * Real.log 2 := by
      rw [linear_add]
      have ha := linear_phaseA_le hx
      push_cast
      nlinarith
    have hlB : linear (m + phaseB) x ≤ (R + 1 : ℕ) * Real.log 2 := by
      rw [linear_add]
      have hb := linear_phaseB_le hx
      push_cast
      nlinarith
    have h0 : ‖jet A B js m x‖ ≤ K := ih m (R + 1) hm0 hl0
    have hA : ‖jet A B js (m + phaseA) x‖ ≤ K :=
      ih (m + phaseA) (R + 1) hmA hlA
    have hB : ‖jet A B js (m + phaseB) x‖ ≤ K :=
      ih (m + phaseB) (R + 1) hmB hlB
    have hsum : (R : ℝ) + 2 * Real.pi * |A| + 2 * Real.pi * |B| ≤ T := by
      have hv := mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 2 * Real.pi)
      dsimp [T]
      push_cast
      nlinarith [show (0 : ℝ) ≤ js.length by positivity]
    calc
      ‖jet A B (j :: js) m x‖ ≤
          ‖(m j : ℂ) * jet A B js m x‖ +
          ‖coeffA A j * jet A B js (m + phaseA) x‖ +
          ‖coeffB B j * jet A B js (m + phaseB) x‖ := by
        rw [jet]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (R : ℝ) * K + (2 * Real.pi * |A|) * K +
          (2 * Real.pi * |B|) * K := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        · exact hm j
        · exact norm_coeffA_le A j
        · exact norm_coeffB_le B j
      _ ≤ T * K := by nlinarith [mul_le_mul_of_nonneg_right hsum hK]
      _ = _ := by
        simp only [List.length_cons]
        have he : R + (js.length + 1) = R + 1 + js.length := by omega
        rw [he, pow_succ]
        dsimp [T, K]
        ring

/-- All mixed derivatives of order `n`, including repeated-coordinate ones,
have an explicit degree-`n` polynomial loss in the phase size. -/
theorem norm_weight_jet_le (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (js : List (Fin 5)) (x : Point) (hx : logBox x) :
    ‖jet A B js amplitude x‖ ≤
      (2 : ℝ) ^ (1 + js.length) *
        ((1 + js.length : ℕ) + 2 * Real.pi * V) ^ js.length := by
  apply norm_jet_le A B V hV js amplitude x hx 1
  · norm_num [Fin.forall_fin_succ, amplitude]
  · have h1 := (hx 1).1
    have h3 := (hx 3).1
    have h4 := (hx 4).1
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simp [linear, amplitude, Fin.sum_univ_succ]
    linarith

/-- A single degree-five loss controls all the derivatives required for
five-dimensional partial summation. -/
theorem norm_weight_jet_le_five (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (js : List (Fin 5)) (hn : js.length ≤ 5) (x : Point) (hx : logBox x) :
    ‖jet A B js amplitude x‖ ≤
      64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 := by
  have hV0 : 0 ≤ V := le_trans (by positivity : 0 ≤ |A| + |B|) hV
  have hN : ((1 + js.length : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (by omega : 1 + js.length ≤ 6)
  have hpi := Real.pi_pos
  have hbase : 1 ≤ 6 + 2 * Real.pi * V := by
    nlinarith [mul_nonneg hpi.le hV0]
  calc
    ‖jet A B js amplitude x‖ ≤
        (2 : ℝ) ^ (1 + js.length) *
          ((1 + js.length : ℕ) + 2 * Real.pi * V) ^ js.length :=
      norm_weight_jet_le A B V hV js x hx
    _ ≤ (2 : ℝ) ^ 6 * (6 + 2 * Real.pi * V) ^ 5 := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
      · exact (pow_le_pow_left₀ (by positivity) (by linarith) js.length).trans
          (pow_le_pow_right₀ hbase hn)
      · positivity
      · positivity
    _ ≤ 64 * ((6 + 2 * Real.pi) * (1 + V)) ^ 5 := by
      norm_num only [show (2 : ℝ) ^ 6 = 64 by norm_num]
      gcongr
      nlinarith
    _ = _ := by rw [mul_pow]; ring

/-- The exact normalized kernel in the original positive variables. -/
def normalizedWeight (A B : ℝ) (v : Point) : ℂ :=
  (((v 1 * v 3 * v 4)⁻¹ : ℝ) : ℂ) *
    Complex.exp (Complex.I * (2 * Real.pi) *
      ((A * v 0 / (v 1 * v 3 * v 4) +
        B * v 0 / (v 1 * v 2 * v 3 * v 4) : ℝ) : ℂ))

theorem weight_log_eq_normalizedWeight (A B : ℝ) (v : Point)
    (hv : ∀ i, 0 < v i) :
    weight A B (fun i => Real.log (v i)) = normalizedWeight A B v := by
  have hexp (i : Fin 5) : Real.exp (Real.log (v i)) = v i := Real.exp_log (hv i)
  have hA : Real.exp (linear phaseA (fun i => Real.log (v i))) =
      v 0 / (v 1 * v 3 * v 4) := by
    simp [linear, phaseA, Fin.sum_univ_succ, Real.exp_add, Real.exp_neg, hexp,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    ring
  have hB : Real.exp (linear phaseB (fun i => Real.log (v i))) =
      v 0 / (v 1 * v 2 * v 3 * v 4) := by
    simp [linear, phaseB, Fin.sum_univ_succ, Real.exp_add, Real.exp_neg, hexp,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    ring
  have hm : Real.exp (linear amplitude (fun i => Real.log (v i))) =
      (v 1 * v 3 * v 4)⁻¹ := by
    simp [linear, amplitude, Fin.sum_univ_succ, Real.exp_add, Real.exp_neg, hexp,
      mul_assoc, mul_comm]
  unfold weight atom normalizedWeight
  rw [Complex.exp_add, ← Complex.ofReal_exp, hm, hA, hB]
  congr 2
  push_cast
  ring

theorem log_mem_logBox (v : Point) (hv : ∀ i, 1 ≤ v i ∧ v i ≤ 2) :
    logBox (fun i => Real.log (v i)) := by
  intro i
  exact ⟨Real.log_nonneg (hv i).1,
    Real.log_le_log (by linarith [(hv i).1]) (hv i).2⟩

/-- Application-ready positive-shell form. These are actual logarithmic mixed
derivatives of `normalizedWeight`; `weight_log_eq_normalizedWeight` identifies
the underlying weight, and `hasDerivAt_jet` certifies every derivative step. -/
theorem normalized_log_mixed_bound (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (js : List (Fin 5)) (hn : js.length ≤ 5) (v : Point)
    (hv : ∀ i, 1 ≤ v i ∧ v i ≤ 2) :
    ‖jet A B js amplitude (fun i => Real.log (v i))‖ ≤
      64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 :=
  norm_weight_jet_le_five A B V hV js hn _ (log_mem_logBox v hv)

end LiLiuPrereqFouvry.SlowFactor
