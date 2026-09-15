import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# The Jurkat--Richert delay functions by finite method of steps

We construct the weighted functions `u F(u)` and `u f(u)` from constant initial
data, rather than postulating a delay-equation contract. Each finite approximant
is continuous and the approximants stabilize on successively larger half-lines.
The harmless cutoffs below extend the weighted functions to the whole real line;
the sieve functions themselves are used only on the positive half-line.

The normalization is (5.5), and the integral and differential recurrences are
(5.7) and (5.6) of Jurkat--Richert (1965). No asymptotic estimates are asserted.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- `false` selects the upper function; `true` selects the lower function. -/
def delayInitial (A : ℝ) (b : Bool) : ℝ := if b then 0 else A

/-- Finite method of steps for the weighted pair. The denominator is truncated
only outside the domain of integration, where its value is immaterial. -/
def delayStep (A : ℝ) : ℕ → Bool → ℝ → ℝ
  | 0, b, _ => delayInitial A b
  | n + 1, b, u => delayInitial A b +
      ∫ t in (2 : ℝ)..max 2 u, delayStep A n (!b) (t - 1) / max 1 (t - 1)

theorem delayStep_initial (A : ℝ) (n : ℕ) (b : Bool) {u : ℝ} (hu : u ≤ 2) :
    delayStep A n b u = delayInitial A b := by
  cases n <;> simp [delayStep, max_eq_left hu]

theorem continuous_delayStep (A : ℝ) (n : ℕ) (b : Bool) :
    Continuous (delayStep A n b) := by
  induction n generalizing b with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun t : ℝ =>
        delayStep A n (!b) (t - 1) / max 1 (t - 1)) :=
      ((ih (!b)).comp (continuous_id.sub continuous_const)).div
        (continuous_const.max (continuous_id.sub continuous_const))
        (fun t => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    exact continuous_const.add
      ((intervalIntegral.continuous_primitive (fun a c => hc.intervalIntegrable a c) 2).comp
        (continuous_const.max continuous_id))

/-- One more step does not change the solution on the already constructed range. -/
theorem delayStep_succ_eq (A : ℝ) (n : ℕ) (b : Bool) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 2) :
    delayStep A (n + 1) b u = delayStep A n b u := by
  induction n generalizing b u with
  | zero =>
    rw [delayStep_initial A 1 b (by simpa using hu), delayStep_initial A 0 b (by simpa using hu)]
  | succ n ih =>
    simp only [delayStep]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ max 2 u := (uIcc_of_le (le_max_left 2 u) ▸ ht).2
    have hb : t - 1 ≤ (n : ℝ) + 2 := by
      have : max 2 u ≤ (n : ℝ) + 3 := max_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by
        push_cast at hu
        linarith)
      linarith
    change delayStep A (n + 1) (!b) (t - 1) / max 1 (t - 1) =
      delayStep A n (!b) (t - 1) / max 1 (t - 1)
    rw [ih (!b) hb]

theorem delayStep_eq_of_le (A : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (b : Bool) {u : ℝ} (hu : u ≤ (n : ℝ) + 2) :
    delayStep A m b u = delayStep A n b u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [delayStep_succ_eq A m b (le_trans hu (by exact_mod_cast Nat.add_le_add_right hnm 2))]
    exact ih

/-- A globally defined weighted function, requiring only finitely many integrals
at any argument. The ceiling is only a choice of a sufficiently large step. -/
def delayWeight (A : ℝ) (b : Bool) (u : ℝ) : ℝ :=
  delayStep A ⌈u⌉₊ b u

/-- Any sufficiently advanced finite step computes the global function exactly. -/
theorem delayWeight_eq_step (A : ℝ) (n : ℕ) (b : Bool) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 2) :
    delayWeight A b u = delayStep A n b u := by
  unfold delayWeight
  rcases le_total n ⌈u⌉₊ with h | h
  · exact delayStep_eq_of_le A h b hu
  · exact (delayStep_eq_of_le A h b (by linarith [Nat.le_ceil u])).symm

theorem delayWeight_initial (A : ℝ) (b : Bool) {u : ℝ} (hu : u ≤ 2) :
    delayWeight A b u = delayInitial A b := by
  rw [delayWeight_eq_step A 0 b (by simpa using hu)]
  rfl

theorem continuous_delayWeight (A : ℝ) (b : Bool) :
    Continuous (delayWeight A b) := by
  rw [continuous_iff_continuousAt]
  intro u
  apply (continuous_delayStep A ⌈u⌉₊ b).continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (by linarith [Nat.le_ceil u] :
    u < (⌈u⌉₊ : ℝ) + 2)] with v hv
  exact delayWeight_eq_step A ⌈u⌉₊ b hv.le

/-- The globally continuous delayed integrand, including an irrelevant extension
to the left of the initial endpoint. -/
def delayIntegrand (A : ℝ) (b : Bool) (t : ℝ) : ℝ :=
  delayWeight A (!b) (t - 1) / max 1 (t - 1)

theorem continuous_delayIntegrand (A : ℝ) (b : Bool) :
    Continuous (delayIntegrand A b) :=
  ((continuous_delayWeight A (!b)).comp (continuous_id.sub continuous_const)).div
    (continuous_const.max (continuous_id.sub continuous_const))
    (fun _t => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

/-- The global integral equation, proved by stabilization, not assumed. -/
theorem delayWeight_integral (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 ≤ u) :
    delayWeight A b u = delayInitial A b + ∫ t in (2 : ℝ)..u, delayIntegrand A b t := by
  rw [delayWeight_eq_step A (⌈u⌉₊ + 1) b (by
    have := Nat.le_ceil u
    push_cast
    linarith), delayStep, max_eq_right hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ≤ u := (uIcc_of_le hu ▸ ht).2
  unfold delayIntegrand
  rw [delayWeight_eq_step A ⌈u⌉₊ (!b) (by linarith [Nat.le_ceil u])]

/-- The unweighted delay pair with arbitrary initial upper constant. -/
def delayFunction (A : ℝ) (b : Bool) (u : ℝ) : ℝ := delayWeight A b u / u

theorem mul_delayFunction (A : ℝ) (b : Bool) {u : ℝ} (hu : u ≠ 0) :
    u * delayFunction A b u = delayWeight A b u := by
  unfold delayFunction
  field_simp

theorem delayFunction_initial (A : ℝ) (b : Bool) {u : ℝ} (hu : u ≤ 2) :
    delayFunction A b u = delayInitial A b / u := by
  rw [delayFunction, delayWeight_initial A b hu]

theorem continuousOn_delayFunction (A : ℝ) (b : Bool) :
    ContinuousOn (delayFunction A b) (Ioi 0) :=
  (continuous_delayWeight A b).continuousOn.div continuousOn_id
    (fun _ hu => ne_of_gt hu)

theorem delayIntegrand_eq (A : ℝ) (b : Bool) {t : ℝ} (ht : 2 ≤ t) :
    delayIntegrand A b t = delayFunction A (!b) (t - 1) := by
  simp only [delayIntegrand, delayFunction, max_eq_right (by linarith : 1 ≤ t - 1)]

/-- Formula (5.7), for the explicitly constructed pair. -/
theorem delayFunction_integral_recurrence (A : ℝ) (b : Bool) {v u : ℝ}
    (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * delayFunction A b u =
      v * delayFunction A b v + ∫ t in v..u, delayFunction A (!b) (t - 1) := by
  have hu : 2 ≤ u := hv.trans hvu
  rw [mul_delayFunction A b (by linarith), mul_delayFunction A b (by linarith),
    delayWeight_integral A b hu, delayWeight_integral A b hv]
  have hc := continuous_delayIntegrand A b
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 2 v) (hc.intervalIntegrable v u)
  have heq : (∫ t in v..u, delayIntegrand A b t) =
      ∫ t in v..u, delayFunction A (!b) (t - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact delayIntegrand_eq A b (hv.trans (uIcc_of_le hvu ▸ ht).1)
  rw [heq] at hadd
  linarith

theorem hasDerivAt_delayWeight (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (delayWeight A b) (delayFunction A (!b) (u - 1)) u := by
  have hd := ((continuous_delayIntegrand A b).integral_hasStrictDerivAt 2 u).hasDerivAt
  rw [delayIntegrand_eq A b hu.le] at hd
  apply (hd.const_add (delayInitial A b)).congr_of_eventuallyEq
  filter_upwards [eventually_ge_nhds hu] with v hv
  exact delayWeight_integral A b hv

/-- The right derivative at the initial endpoint, included in (5.6). -/
theorem hasDerivWithinAt_delayWeight_two (A : ℝ) (b : Bool) :
    HasDerivWithinAt (delayWeight A b) (delayFunction A (!b) 1) (Ici 2) 2 := by
  have hd := ((continuous_delayIntegrand A b).integral_hasStrictDerivAt 2 2).hasDerivAt
  rw [delayIntegrand_eq A b le_rfl] at hd
  norm_num only at hd
  exact (hd.const_add (delayInitial A b)).hasDerivWithinAt.congr
    (fun _ hv => delayWeight_integral A b hv) (delayWeight_integral A b le_rfl)

/-- The literal weighted differential equation (5.6) away from the endpoint. -/
theorem hasDerivAt_mul_delayFunction (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun x => x * delayFunction A b x)
      (delayFunction A (!b) (u - 1)) u := by
  apply (hasDerivAt_delayWeight A b hu).congr_of_eventuallyEq
  filter_upwards [eventually_ge_nhds hu] with v hv
  exact mul_delayFunction A b (by linarith)

theorem hasDerivWithinAt_mul_delayFunction_two (A : ℝ) (b : Bool) :
    HasDerivWithinAt (fun x => x * delayFunction A b x)
      (delayFunction A (!b) 1) (Ici 2) 2 := by
  exact (hasDerivWithinAt_delayWeight_two A b).congr
    (fun _ hv => mul_delayFunction A b (by
      have : (2 : ℝ) ≤ _ := hv
      linarith)) (mul_delayFunction A b (by norm_num))

/-- Uniqueness of the integral initial-value problem on the positive half-line.
This is a consequence of the construction, not an input to it. -/
theorem delayFunction_unique (A : ℝ) (k : Bool → ℝ → ℝ)
    (hinit : ∀ b u, 0 < u → u ≤ 2 → k b u = delayInitial A b / u)
    (hint : ∀ b u, 2 ≤ u →
      u * k b u = delayInitial A b + ∫ t in (2 : ℝ)..u, k (!b) (t - 1)) :
    ∀ b u, 0 < u → k b u = delayFunction A b u := by
  have hstep : ∀ n : ℕ, ∀ b u, 0 < u → u ≤ (n : ℝ) + 2 →
      k b u = delayFunction A b u := by
    intro n
    induction n with
    | zero =>
      intro b u hu hb
      have hb' : u ≤ 2 := by simpa using hb
      rw [hinit b u hu hb', delayFunction_initial A b hb']
    | succ n ih =>
      intro b u hu hb
      by_cases hsmall : u ≤ 2
      · rw [hinit b u hu hsmall, delayFunction_initial A b hsmall]
      have hlarge : 2 ≤ u := le_of_lt (lt_of_not_ge hsmall)
      apply mul_left_cancel₀ (ne_of_gt hu)
      rw [hint b u hlarge, mul_delayFunction A b (ne_of_gt hu),
        delayWeight_integral A b hlarge]
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc 2 u := by simpa only [uIcc_of_le hlarge] using ht
      rw [delayIntegrand_eq A b ht'.1]
      apply ih (!b) (t - 1) (by linarith [ht'.1])
      push_cast at hb
      linarith [ht'.2]
  intro b u hu
  exact hstep ⌈u⌉₊ b u hu (by linarith [Nat.le_ceil u])

theorem delayStep_nonneg {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (b : Bool) (u : ℝ) :
    0 ≤ delayStep A n b u := by
  have hi : ∀ b, 0 ≤ delayInitial A b := by
    intro b
    cases b
    · exact hA
    · exact le_rfl
  induction n generalizing b u with
  | zero => exact hi b
  | succ n ih =>
    apply add_nonneg (hi b)
    apply intervalIntegral.integral_nonneg (le_max_left 2 u)
    intro t _
    exact div_nonneg (ih (!b) (t - 1)) (le_trans zero_le_one (le_max_left _ _))

theorem delayInitial_le_delayWeight {A : ℝ} (hA : 0 ≤ A) (b : Bool) (u : ℝ) :
    delayInitial A b ≤ delayWeight A b u := by
  rw [delayWeight_eq_step A (⌈u⌉₊ + 1) b (by
    push_cast
    linarith [Nat.le_ceil u])]
  change delayInitial A b ≤ delayInitial A b + _
  apply le_add_of_nonneg_right
  apply intervalIntegral.integral_nonneg (le_max_left 2 u)
  intro t _
  exact div_nonneg (delayStep_nonneg hA _ (!b) (t - 1))
    (le_trans zero_le_one (le_max_left _ _))

/-- The normalization constant from Jurkat--Richert (5.5). -/
def jr1965DelayConstant : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

/-- The actual global upper delay function, constructed by finite method of steps.
This is not the legacy placeholder `sieveFunctionF`. -/
def jr1965F : ℝ → ℝ := delayFunction jr1965DelayConstant false

/-- The actual global lower delay function, constructed by finite method of steps.
This is not the legacy placeholder `sieveFunctionf`. -/
def jr1965f : ℝ → ℝ := delayFunction jr1965DelayConstant true

theorem jr1965F_initial {u : ℝ} (hu : u ≤ 2) :
    jr1965F u = 2 * Real.exp Real.eulerMascheroniConstant / u := by
  simpa [jr1965F, jr1965DelayConstant, delayInitial] using
    delayFunction_initial jr1965DelayConstant false hu

theorem jr1965f_initial {u : ℝ} (hu : u ≤ 2) : jr1965f u = 0 := by
  simpa [jr1965f, delayInitial] using delayFunction_initial jr1965DelayConstant true hu

theorem continuousOn_jr1965F : ContinuousOn jr1965F (Ioi 0) :=
  continuousOn_delayFunction jr1965DelayConstant false

theorem continuousOn_jr1965f : ContinuousOn jr1965f (Ioi 0) :=
  continuousOn_delayFunction jr1965DelayConstant true

theorem jr1965F_integral_recurrence {v u : ℝ} (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * jr1965F u = v * jr1965F v + ∫ t in v..u, jr1965f (t - 1) :=
  delayFunction_integral_recurrence jr1965DelayConstant false hv hvu

theorem jr1965f_integral_recurrence {v u : ℝ} (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * jr1965f u = v * jr1965f v + ∫ t in v..u, jr1965F (t - 1) :=
  delayFunction_integral_recurrence jr1965DelayConstant true hv hvu

theorem hasDerivAt_mul_jr1965F {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun x => x * jr1965F x) (jr1965f (u - 1)) u :=
  hasDerivAt_mul_delayFunction jr1965DelayConstant false hu

theorem hasDerivAt_mul_jr1965f {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun x => x * jr1965f x) (jr1965F (u - 1)) u :=
  hasDerivAt_mul_delayFunction jr1965DelayConstant true hu

theorem hasDerivWithinAt_mul_jr1965F_two :
    HasDerivWithinAt (fun x => x * jr1965F x) (jr1965f 1) (Ici 2) 2 :=
  hasDerivWithinAt_mul_delayFunction_two jr1965DelayConstant false

theorem hasDerivWithinAt_mul_jr1965f_two :
    HasDerivWithinAt (fun x => x * jr1965f x) (jr1965F 1) (Ici 2) 2 :=
  hasDerivWithinAt_mul_delayFunction_two jr1965DelayConstant true

theorem jr1965F_pos {u : ℝ} (hu : 0 < u) : 0 < jr1965F u := by
  have hA : 0 < jr1965DelayConstant := by
    unfold jr1965DelayConstant
    positivity
  exact div_pos (lt_of_lt_of_le hA (delayInitial_le_delayWeight hA.le false u)) hu

theorem jr1965f_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ jr1965f u :=
  div_nonneg (delayStep_nonneg (by unfold jr1965DelayConstant; positivity) _ true u) hu.le

/-- The first extended upper formula, Jurkat--Richert (5.8). -/
theorem jr1965F_eq_of_le_three {u : ℝ} (hu : u ≤ 3) :
    jr1965F u = 2 * Real.exp Real.eulerMascheroniConstant / u := by
  by_cases hsmall : u ≤ 2
  · exact jr1965F_initial hsmall
  have hlarge : 2 ≤ u := le_of_lt (lt_of_not_ge hsmall)
  have h := jr1965F_integral_recurrence le_rfl hlarge
  have hz : (∫ t in (2 : ℝ)..u, jr1965f (t - 1)) = 0 := by
    calc
      _ = ∫ _t in (2 : ℝ)..u, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact jr1965f_initial (by have := (uIcc_of_le hlarge ▸ ht).2; linarith)
      _ = 0 := by simp
  rw [hz, jr1965F_initial le_rfl] at h
  apply (eq_div_iff (by linarith : u ≠ 0)).2
  nlinarith

/-- The parity-indexed notation (5.14). -/
def jr1965g (ν : ℕ) (u : ℝ) : ℝ := if Even ν then jr1965F u else jr1965f u

theorem jr1965g_integral_recurrence (ν : ℕ) {v u : ℝ} (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * jr1965g ν u = v * jr1965g ν v + ∫ t in v..u, jr1965g (ν + 1) (t - 1) := by
  by_cases hν : Even ν
  · simpa [jr1965g, Nat.even_add_one, hν] using jr1965F_integral_recurrence hv hvu
  · simpa [jr1965g, Nat.even_add_one, hν] using jr1965f_integral_recurrence hv hvu

theorem continuousOn_jr1965g (ν : ℕ) : ContinuousOn (jr1965g ν) (Ioi 0) := by
  unfold jr1965g
  split_ifs
  · exact continuousOn_jr1965F
  · exact continuousOn_jr1965f

theorem hasDerivAt_mul_jr1965g (ν : ℕ) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun x => x * jr1965g ν x) (jr1965g (ν + 1) (u - 1)) u := by
  by_cases hν : Even ν
  · simpa [jr1965g, Nat.even_add_one, hν] using hasDerivAt_mul_jr1965F hu
  · simpa [jr1965g, Nat.even_add_one, hν] using hasDerivAt_mul_jr1965f hu

end MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
