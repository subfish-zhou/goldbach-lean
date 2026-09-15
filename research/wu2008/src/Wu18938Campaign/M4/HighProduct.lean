import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
namespace Wu18938Campaign.M4
open Real

private theorem list_product_bound (l : List ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hl : ∀ p ∈ l, (p : ℝ) ≤ X) :
    (l.prod : ℝ) ≤ X ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.prod_cons, Nat.cast_mul, List.length_cons, pow_succ]
    have hp := hl p (by simp)
    have htail := ih (fun q hq => hl q (by simp [hq]))
    calc
      (p : ℝ) * l.prod ≤ X * X ^ l.length :=
        mul_le_mul hp htail (Nat.cast_nonneg _) hX
      _ = X ^ l.length * X := mul_comm _ _

theorem six_label_product_bound {N d : ℕ} (hN : 2 ≤ N) (l : List ℕ)
    (hlen : l.length ≤ 6)
    (hd : (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hl : ∀ p ∈ l, (p : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) :
    ((d * l.prod : ℕ) : ℝ) ≤ (N : ℝ) ^ (3127 / 3981 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbase : 1 ≤ (N : ℝ) ^ (100 / 1327 : ℝ) :=
    one_le_rpow hN1 (by norm_num)
  have hprod := (list_product_bound l (le_trans zero_le_one hbase) hl).trans
    (pow_le_pow_right₀ hbase hlen)
  rw [Nat.cast_mul]
  calc
    (d : ℝ) * l.prod ≤ (N : ℝ) ^ (1 / 3 : ℝ) *
        ((N : ℝ) ^ (100 / 1327 : ℝ)) ^ 6 :=
      mul_le_mul hd hprod (Nat.cast_nonneg _) (rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (3127 / 3981 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul hN0.le, ← rpow_add hN0]
      norm_num

theorem six_label_square_gap {N d q : ℕ} (hN : 2 ≤ N) (l : List ℕ)
    (hlen : l.length ≤ 6)
    (hd : (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hl : ∀ p ∈ l, (p : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ))
    (hq : (q : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) :
    ((d * l.prod : ℕ) : ℝ) * (q : ℝ) ^ 2 ≤
      (N : ℝ) ^ (3727 / 3981 : ℝ) ∧
    ((d * l.prod : ℕ) : ℝ) * (q : ℝ) ^ 2 < N := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hprod := six_label_product_bound hN l hlen hd hl
  have hq2 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) q) hq 2
  have hbound : ((d * l.prod : ℕ) : ℝ) * (q : ℝ) ^ 2 ≤
      (N : ℝ) ^ (3727 / 3981 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (3127 / 3981 : ℝ) *
          ((N : ℝ) ^ (100 / 1327 : ℝ)) ^ 2 :=
        mul_le_mul hprod hq2 (sq_nonneg _) (rpow_nonneg hN0.le _)
      _ = _ := by
        rw [← rpow_natCast, ← rpow_mul hN0.le, ← rpow_add hN0]
        norm_num
  refine ⟨hbound, hbound.trans_lt ?_⟩
  simpa only [rpow_one] using
    rpow_lt_rpow_of_exponent_lt hN1 (by norm_num : (3727 / 3981 : ℝ) < 1)

theorem six_label_buchstab_range {N d q : ℕ} (hN : 2 ≤ N) (hd0 : 0 < d)
    (l : List ℕ) (hlen : l.length ≤ 6)
    (hd : (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hl : ∀ p ∈ l, 0 < p ∧ (p : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ))
    (hqlo : (N : ℝ) ^ (1 / 40 : ℝ) ≤ q)
    (hqhi : (q : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) :
    2 < log ((N : ℝ) / (d * l.prod : ℕ)) / log q ∧
      log ((N : ℝ) / (d * l.prod : ℕ)) / log q ≤ 40 := by
  let D := d * l.prod
  have hD : 0 < D := Nat.mul_pos hd0 (List.prod_pos (fun p hp => (hl p hp).1))
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hq1 : (1 : ℝ) < q :=
    (one_lt_rpow hN1 (by norm_num : (0 : ℝ) < 1 / 40)).trans_le hqlo
  have hlogq : 0 < log (q : ℝ) := log_pos hq1
  have hgap := (six_label_square_gap hN l hlen hd
    (fun p hp => (hl p hp).2) hqhi).2
  have hx : (q : ℝ) ^ 2 < (N : ℝ) / D := by
    apply (lt_div_iff₀ hDR).mpr
    simpa only [D, mul_comm] using hgap
  have hlog := log_lt_log (sq_pos_of_pos (zero_lt_one.trans hq1)) hx
  rw [log_pow] at hlog
  have hqlog := log_le_log (rpow_pos_of_pos hN0 _) hqlo
  rw [log_rpow hN0] at hqlog
  have hxlog : log ((N : ℝ) / D) ≤ log (N : ℝ) :=
    log_le_log (div_pos hN0 hDR) (div_le_self hN0.le hD1)
  constructor
  · apply (lt_div_iff₀ hlogq).mpr
    simpa only [Nat.cast_ofNat] using hlog
  · apply (div_le_iff₀ hlogq).mpr
    linarith only [hqlog, hxlog]

theorem rough_unit_absorbed {x y τ : ℝ}
    (hy : 1 < y) (hτ : 0 < τ) (hyτ : 1 / τ ≤ y) (hxy : y ^ 2 ≤ x) :
    1 ≤ τ * x / log y := by
  have hlog : 0 < log y := log_pos hy
  have hloghi : log y ≤ y := (log_le_sub_one_of_pos (zero_lt_one.trans hy)).trans
    (by linarith)
  have hτy : 1 ≤ τ * y := by
    have h := (div_le_iff₀ hτ).mp hyτ
    simpa only [mul_comm] using h
  have h1 := mul_le_mul_of_nonneg_right hτy hlog.le
  have h2 := mul_le_mul_of_nonneg_left hloghi
    (mul_nonneg hτ.le (zero_lt_one.trans hy).le)
  have h3 := mul_le_mul_of_nonneg_left hxy hτ.le
  apply (le_div_iff₀ hlog).mpr
  nlinarith only [h1, h2, h3]

end Wu18938Campaign.M4
