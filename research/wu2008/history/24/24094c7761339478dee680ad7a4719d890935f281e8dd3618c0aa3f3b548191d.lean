import MathlibNt.Wu2004MeanValue.SieveErrorPayment
import MathlibNt.Wu2004MeanValue.OriginalDyadicUniform

/-!
# Paying original-target low scales and boundaries

The low-scale rectangle costs `O(N^(3/4))`. The three target boundary
families cost `O(sqrt N * log N)`, not the earlier AP endpoint error.
The positive universal lower bound for the Liu singular series pays both.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.SingularSeries
open scoped BigOperators
noncomputable section

theorem eventually_powerSaving_le_singular_margin (E β ε : ℝ)
    (hE : 0 ≤ E) (hβ : β < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      E * (N : ℝ) ^ β ≤ ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  have hlog := (isLittleO_log_rpow_rpow_atTop 3
    (show 0 < 1 - β by linarith)).bound (show (0 : ℝ) < 1 by norm_num)
  have hlarge : ∀ᶠ x : ℝ in atTop,
      E * x ^ β ≤ E * x / Real.log x ^ (3 : ℝ) := by
    filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with x hl hx
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hl3 : Real.log x ^ (3 : ℝ) ≤ x ^ (1 - β) := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hl0.le _),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hl
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hl0 3)).mpr
    calc
      (E * x ^ β) * Real.log x ^ (3 : ℝ) ≤
          (E * x ^ β) * x ^ (1 - β) :=
        mul_le_mul_of_nonneg_left hl3 (mul_nonneg hE (Real.rpow_nonneg hx0.le _))
      _ = E * x := by rw [mul_assoc, ← Real.rpow_add hx0]; simp
  have hlargeN := tendsto_natCast_atTop_atTop.eventually hlarge
  have hpay := tendsto_natCast_atTop_atTop.eventually
    (eventually_logCube_le_singular_margin E ε hε)
  filter_upwards [hlargeN, hpay] with N hl hp
  exact hl.trans (hp N)

def originalTripleExceptionBudget (x : ℝ) : ℝ :=
  (Real.sqrt (Real.sqrt x) + 1) * (Real.sqrt x + 1) +
    (3 / Real.log 2) * Real.log x * (Real.sqrt x + 1)

theorem eventually_originalTripleExceptionBudget_le :
    ∀ᶠ x : ℝ in atTop,
      originalTripleExceptionBudget x ≤
        (4 + 6 / Real.log 2) * x ^ (3 / 4 : ℝ) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop 1
    (show (0 : ℝ) < 1 / 4 by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with x hl hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlquarter : Real.log x ≤ x ^ (1 / 4 : ℝ) := by
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos hl0,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hl
  have hs1 : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx1
  have hss1 : 1 ≤ Real.sqrt (Real.sqrt x) := by
    simpa using Real.sqrt_le_sqrt hs1
  have hquarter : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  have hproduct : x ^ (1 / 4 : ℝ) * Real.sqrt x = x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  have hlow : (Real.sqrt (Real.sqrt x) + 1) * (Real.sqrt x + 1) ≤
      4 * x ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ (2 * Real.sqrt (Real.sqrt x)) * (2 * Real.sqrt x) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = _ := by rw [hquarter]; nlinarith [hproduct]
  have hboundary : (3 / Real.log 2) * Real.log x * (Real.sqrt x + 1) ≤
      (6 / Real.log 2) * x ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ (3 / Real.log 2) * x ^ (1 / 4 : ℝ) * (2 * Real.sqrt x) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hlquarter (by positivity)
        · linarith
        · positivity
        · positivity
      _ = _ := by
        rw [mul_assoc, mul_left_comm (x ^ (1 / 4 : ℝ)) 2, hproduct]
        ring
  unfold originalTripleExceptionBudget
  nlinarith

theorem eventually_originalTripleExceptionBudget_paid (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      originalTripleExceptionBudget N ≤
        ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbudget := tendsto_natCast_atTop_atTop.eventually
    eventually_originalTripleExceptionBudget_le
  have hpay := eventually_powerSaving_le_singular_margin (4 + 6 / Real.log 2)
    (3 / 4) ε (by positivity) (by norm_num) hε
  filter_upwards [hbudget, hpay] with N hb hp
  exact hb.trans hp

/-- This sum pays the three literal target boundaries, even when their
equalities coincide. Its constants are independent of the dyadic length. -/
theorem dyadic_target_boundary_sum_le {η x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hx : 16 ≤ x) (hfirst : Real.sqrt x ≤ dyadicScale η x 0) :
    3 * (∑ j ∈ range (dyadicLast η x + 1),
      (Real.sqrt (2 * dyadicScale η x j) + 1)) ≤
        (3 / Real.log 2) * Real.log x * (Real.sqrt x + 1) := by
  have hx0 : 0 < x := by linarith
  have hsum : (∑ j ∈ range (dyadicLast η x + 1),
      (Real.sqrt (2 * dyadicScale η x j) + 1)) ≤
        (dyadicLast η x + 1 : ℕ) * (Real.sqrt x + 1) := by
    calc
      _ ≤ ∑ _j ∈ range (dyadicLast η x + 1), (Real.sqrt x + 1) := by
        apply sum_le_sum
        intro j _
        exact add_le_add (Real.sqrt_le_sqrt ((dyadicScale_twice_le hη hx0 j).trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hη1 hx0.le))) le_rfl
      _ = _ := by simp; ring
  have hcount := dyadicLast_add_one_le_log hη hη1 hx hfirst
  calc
    _ ≤ 3 * ((dyadicLast η x + 1 : ℕ) * (Real.sqrt x + 1)) := by linarith
    _ ≤ 3 * (((1 / Real.log 2) * Real.log x) * (Real.sqrt x + 1)) := by
      gcongr
    _ = _ := by ring

end
end Wu2004MeanValue
