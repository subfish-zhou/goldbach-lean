import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Set
open scoped Interval BigOperators
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The unchanged one-dimensional kernel, without its author weight. -/
def g11AuthorKernel (r : ℝ) : ℝ :=
  ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
    2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) / (2 * r)

def g11AuthorPrimitive0 (r : ℝ) : ℝ :=
  (-(Real.log ((4 / 33 : ℝ) / r) ^ 2 -
    4 * Real.log ((4 / 33 : ℝ) / r) + 6) / r +
      2 * Real.log ((4 / 33 : ℝ) / r) / (4 / 33 : ℝ)) / 2

theorem g11AuthorLog_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => Real.log ((4 / 33 : ℝ) / x)) (-1 / r) r := by
  have hd := ((hasDerivAt_const r (4 / 33 : ℝ)).div (hasDerivAt_id r) hr.ne').log
    (div_ne_zero (by norm_num) hr.ne')
  apply hd.congr_deriv
  dsimp
  field_simp
  ring

theorem g11AuthorPrimitive0_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt g11AuthorPrimitive0 (g11AuthorKernel r) r := by
  have hd := g11AuthorLog_hasDerivAt hr
  apply ((((((hd.pow 2).sub (hd.const_mul 4)).add_const 6).neg.div
    (hasDerivAt_id r) hr.ne').add ((hd.const_mul 2).div_const (4 / 33 : ℝ))).div_const 2).congr_deriv
  dsimp [g11AuthorKernel]
  field_simp
  ring

def g11AuthorPrimitive1 (r : ℝ) : ℝ :=
  (-(Real.log ((4 / 33 : ℝ) / r) ^ 3) / 3 +
    Real.log ((4 / 33 : ℝ) / r) ^ 2 - 2 * Real.log ((4 / 33 : ℝ) / r) -
      2 * r / (4 / 33 : ℝ)) / 2

def g11AuthorPrimitiveN (n : ℕ) (r : ℝ) : ℝ :=
  (r ^ (n + 1) / (n + 1) *
    (Real.log ((4 / 33 : ℝ) / r) ^ 2 +
      (2 / (n + 1) - 2) * Real.log ((4 / 33 : ℝ) / r) +
        (2 / (n + 1) ^ 2 - 2 / (n + 1) + 2)) -
    2 * r ^ (n + 2) / ((4 / 33 : ℝ) * (n + 2))) / 2

theorem g11AuthorPrimitive1_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt g11AuthorPrimitive1 (r * g11AuthorKernel r) r := by
  have hd := g11AuthorLog_hasDerivAt hr
  apply ((((((hd.pow 3).neg.div_const 3).add (hd.pow 2)).sub
    (hd.const_mul 2)).sub (((hasDerivAt_id r).const_mul 2).div_const
      (4 / 33 : ℝ))).div_const 2).congr_deriv
  dsimp [g11AuthorKernel]
  field_simp
  ring

theorem g11AuthorPrimitiveN_hasDerivAt (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (g11AuthorPrimitiveN n) (r ^ (n + 2) * g11AuthorKernel r) r := by
  have hd := g11AuthorLog_hasDerivAt hr
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  apply (((((hasDerivAt_id r).pow (n + 1)).div_const ((n : ℝ) + 1)).mul
    (((hd.pow 2).add (hd.const_mul (2 / ((n : ℝ) + 1) - 2))).add_const
      (2 / ((n : ℝ) + 1) ^ 2 - 2 / ((n : ℝ) + 1) + 2))).sub
    ((((hasDerivAt_id r).pow (n + 2)).const_mul 2).div_const
      ((4 / 33 : ℝ) * ((n : ℝ) + 2)))).div_const 2 |>.congr_deriv
  dsimp [g11AuthorKernel]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
  field_simp
  ring

def g11AuthorMajorant (r : ℝ) : ℝ :=
  1 + r + (∑ n ∈ Finset.range 10, r ^ (n + 2)) + (10 / 9 : ℝ) * r ^ 12

def g11AuthorMajorantPrimitive (r : ℝ) : ℝ :=
  g11AuthorPrimitive0 r + g11AuthorPrimitive1 r +
    (∑ n ∈ Finset.range 10, g11AuthorPrimitiveN n r) +
      (10 / 9 : ℝ) * g11AuthorPrimitiveN 10 r

theorem g11AuthorMajorantPrimitive_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt g11AuthorMajorantPrimitive (g11AuthorMajorant r * g11AuthorKernel r) r := by
  have hs := HasDerivAt.fun_sum (u := Finset.range 10)
    (fun n _ => g11AuthorPrimitiveN_hasDerivAt n hr)
  apply ((((g11AuthorPrimitive0_hasDerivAt hr).add
    (g11AuthorPrimitive1_hasDerivAt hr)).add hs).add
    ((g11AuthorPrimitiveN_hasDerivAt 10 hr).const_mul (10 / 9 : ℝ))).congr_deriv
  dsimp [g11AuthorMajorant]
  rw [← Finset.sum_mul]
  ring

theorem g11AuthorMajorant_geometric {r : ℝ} (hr : 0 ≤ r) (hrc : r ≤ 1 / 10) :
    1 / (1 - r) ≤ g11AuthorMajorant r := by
  have hden : 0 < 1 - r := by linarith
  apply (div_le_iff₀ hden).2
  have hp : 0 ≤ r ^ 12 * (1 - 10 * r) := mul_nonneg (pow_nonneg hr _) (by linarith)
  have he : g11AuthorMajorant r * (1 - r) - 1 = r ^ 12 * (1 - 10 * r) / 9 := by
    norm_num [g11AuthorMajorant, Finset.sum_range_succ]
    ring
  linarith

theorem g11AuthorKernel_nonneg {r : ℝ} (hr : 0 < r) (hrb : r ≤ 4 / 33) :
    0 ≤ g11AuthorKernel r := by
  have hi : 0 ≤ ∫ q in r..(4 / 33 : ℝ), Real.log ((4 / 33 : ℝ) / q) ^ 2 / q ^ 2 :=
    intervalIntegral.integral_nonneg hrb (fun q _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [goldbachG11PrimeIntegral_qIntegral hr hrb] at hi
  exact div_nonneg hi (by positivity)

theorem g11AuthorKernel_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn g11AuthorKernel (Icc a b) := by
  have hn : ∀ r ∈ Icc a b, r ≠ 0 := fun _ hr => (ha.trans_le hr.1).ne'
  have hl : ContinuousOn (fun r : ℝ => Real.log ((4 / 33 : ℝ) / r)) (Icc a b) :=
    (continuousOn_const.div continuousOn_id hn).log
      (fun r hr => div_ne_zero (by norm_num) (hn r hr))
  exact (((((hl.pow 2).sub (hl.const_mul 2)).add_const 2).div continuousOn_id hn).sub
    continuousOn_const).div (continuousOn_const.mul continuousOn_id)
      (fun r hr => mul_ne_zero (by norm_num) (hn r hr))

theorem continuous_g11AuthorMajorant : Continuous g11AuthorMajorant := by
  unfold g11AuthorMajorant
  fun_prop

theorem g11AuthorMajorant_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in a..b, g11AuthorMajorant r * g11AuthorKernel r) =
      g11AuthorMajorantPrimitive b - g11AuthorMajorantPrimitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => g11AuthorMajorantPrimitive_hasDerivAt
      (ha.trans_le (by rwa [uIcc_of_le hab] at hr : r ∈ Icc a b).1))
    ((continuous_g11AuthorMajorant.continuousOn.mul (g11AuthorKernel_continuousOn ha)).intervalIntegrable_of_Icc hab)

theorem g11AuthorKernel_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in a..b, g11AuthorKernel r) = g11AuthorPrimitive0 b - g11AuthorPrimitive0 a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => g11AuthorPrimitive0_hasDerivAt
      (ha.trans_le (by rwa [uIcc_of_le hab] at hr : r ∈ Icc a b).1))
    ((g11AuthorKernel_continuousOn ha).intervalIntegrable_of_Icc hab)

/-- An unconditional analytic upper bound by explicit endpoint primitives. -/
theorem goldbachG11PrimeIntegral_author_le_primitives :
    goldbachG11PrimeIntegral goldbachG11AuthorWeight ≤
      (36 / 5 : ℝ) * (g11AuthorMajorantPrimitive (1 / 10) -
        g11AuthorMajorantPrimitive (4 / 53)) +
      8 * (g11AuthorPrimitive0 (4 / 33) - g11AuthorPrimitive0 (1 / 10)) := by
  have hlow : (∫ r in (4 / 53 : ℝ)..(1 / 10), g11AuthorKernel r / (1 - r)) ≤
      ∫ r in (4 / 53 : ℝ)..(1 / 10), g11AuthorMajorant r * g11AuthorKernel r := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((g11AuthorKernel_continuousOn (by norm_num : (0 : ℝ) < 4 / 53)).div
        (continuousOn_const.sub continuousOn_id)
          (fun r hr => by change 1 - r ≠ 0; linarith [hr.2])).intervalIntegrable_of_Icc (by norm_num))
      ((continuous_g11AuthorMajorant.continuousOn.mul
        (g11AuthorKernel_continuousOn (by norm_num : (0 : ℝ) < 4 / 53))).intervalIntegrable_of_Icc
          (by norm_num))
    intro r hr
    have hr0 : 0 < r := by linarith [hr.1]
    have hm := mul_le_mul_of_nonneg_right (g11AuthorMajorant_geometric hr0.le hr.2)
      (g11AuthorKernel_nonneg hr0 (by linarith [hr.2]))
    change g11AuthorKernel r / (1 - r) ≤ g11AuthorMajorant r * g11AuthorKernel r
    simpa [div_eq_mul_inv, mul_comm] using hm
  rw [g11AuthorMajorant_integral (by norm_num : (0 : ℝ) < 4 / 53) (by norm_num)] at hlow
  have he : goldbachG11PrimeIntegral goldbachG11AuthorWeight =
      (36 / 5 : ℝ) * (∫ r in (4 / 53 : ℝ)..(1 / 10), g11AuthorKernel r / (1 - r)) +
        8 * (∫ r in (1 / 10 : ℝ)..(4 / 33), g11AuthorKernel r) := by
    rw [goldbachG11PrimeIntegral_author_split]
    congr 2
    apply intervalIntegral.integral_congr
    intro r _
    simp only [g11AuthorKernel, div_eq_mul_inv, mul_inv]
    ring
  rw [he, g11AuthorKernel_integral (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num)]
  linarith

#check goldbachG11PrimeIntegral_author_le_primitives
#print axioms goldbachG11PrimeIntegral_author_le_primitives
#check g11AuthorMajorant_geometric
#print axioms g11AuthorMajorant_geometric
#check g11AuthorMajorant_integral
#print axioms g11AuthorMajorant_integral
#check g11AuthorPrimitive0_hasDerivAt
#print axioms g11AuthorPrimitive0_hasDerivAt
#check g11AuthorPrimitive1_hasDerivAt
#print axioms g11AuthorPrimitive1_hasDerivAt
#check g11AuthorPrimitiveN_hasDerivAt
#print axioms g11AuthorPrimitiveN_hasDerivAt
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig