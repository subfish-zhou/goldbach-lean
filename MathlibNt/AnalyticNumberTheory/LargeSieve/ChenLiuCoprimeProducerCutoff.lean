import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEquation223Source

/-!
# The real cutoff in Pan--Wang--Ding (2.26)

On printed pp. 600 and 603 the parameters are
`D₁ = log(x)^B`, `D = sqrt(x)/log(x)^B`, and `H = (2^j D₁)^2`.
The integer endpoint of the short polynomial is the floor of the *real*
square, not the square of a rounded conductor. The conductor interval is
open on the left and closed on the right, including at integral endpoints.
-/

noncomputable section
open Classical Complex Finset MeasureTheory Filter
open scoped BigOperators Topology

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

def lowConductor (x : ℕ) (B : ℝ) : ℝ := Real.log x ^ B

def upperConductor (x : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt x / lowConductor x B

def conductorRadius (x : ℕ) (B : ℝ) (j : ℕ) : ℝ :=
  2 ^ j * lowConductor x B

def shortCutoff (R : ℝ) : ℕ := ⌊R ^ 2⌋₊

def conductorCell (R : ℝ) : Finset ℕ := Ioc ⌊R⌋₊ ⌊2 * R⌋₊

theorem mem_conductorCell_iff {R : ℝ} (hR : 0 ≤ R) (q : ℕ) :
    q ∈ conductorCell R ↔ R < q ∧ (q : ℝ) ≤ 2 * R := by
  simp only [conductorCell, mem_Ioc, Nat.floor_lt hR,
    Nat.le_floor_iff (by positivity : 0 ≤ 2 * R)]

theorem le_shortCutoff_iff (R : ℝ) (n : ℕ) :
    n ≤ shortCutoff R ↔ (n : ℝ) ≤ R ^ 2 :=
  Nat.le_floor_iff (sq_nonneg R)


theorem shortCutoff_le_square (R : ℝ) : (shortCutoff R : ℝ) ≤ R ^ 2 :=
  Nat.floor_le (sq_nonneg R)

theorem square_lt_shortCutoff_add_one (R : ℝ) :
    R ^ 2 < (shortCutoff R : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem shortCutoff_pos {R : ℝ} (hR : 1 ≤ R) : 1 ≤ shortCutoff R := by
  apply (le_shortCutoff_iff R 1).mpr
  simp only [Nat.cast_one]
  nlinarith

theorem square_le_two_mul_shortCutoff {R : ℝ} (hR : 1 ≤ R) :
    R ^ 2 ≤ 2 * (shortCutoff R : ℝ) := by
  have hH : (1 : ℝ) ≤ shortCutoff R := by exact_mod_cast shortCutoff_pos hR
  linarith [square_lt_shortCutoff_add_one R]

theorem radius_le_two_mul_floor {R : ℝ} (hR : 1 ≤ R) :
    R ≤ 2 * (⌊R⌋₊ : ℝ) := by
  have hfloor : (1 : ℝ) ≤ ⌊R⌋₊ := by
    have hn : 1 ≤ ⌊R⌋₊ :=
      (Nat.le_floor_iff (by linarith : 0 ≤ R)).mpr (by simpa using hR)
    exact_mod_cast hn
  linarith [Nat.lt_floor_add_one R]

theorem lowConductor_ge_one {x : ℕ} {B : ℝ}
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) : 1 ≤ lowConductor x B :=
  Real.one_le_rpow hx hB

theorem conductorRadius_ge_one {x : ℕ} {B : ℝ} (j : ℕ)
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) : 1 ≤ conductorRadius x B j := by
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  exact one_le_mul_of_one_le_of_one_le hp (lowConductor_ge_one hx hB)

theorem upperConductor_square (x : ℕ) (B : ℝ) :
    upperConductor x B ^ 2 = (x : ℝ) / lowConductor x B ^ 2 := by
  rw [upperConductor, div_pow, Real.sq_sqrt (Nat.cast_nonneg x)]

theorem upperConductor_le_sqrt {x : ℕ} {B : ℝ}
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) :
    upperConductor x B ≤ Real.sqrt x := by
  exact div_le_self (Real.sqrt_nonneg _) (lowConductor_ge_one hx hB)

/-- The hypothesis required by the proved contour displacement follows from
the actual active-cell inequality, uniformly in the cell index. -/
theorem shortCutoff_le_x {x : ℕ} {B R : ℝ}
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hRD : R ≤ upperConductor x B) : shortCutoff R ≤ x := by
  apply Nat.floor_le_of_le
  have hRs := hRD.trans (upperConductor_le_sqrt hx hB)
  calc
    R ^ 2 ≤ (Real.sqrt x) ^ 2 := pow_le_pow_left₀ hR hRs 2
    _ = (x : ℝ) := Real.sq_sqrt (Nat.cast_nonneg x)


end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
