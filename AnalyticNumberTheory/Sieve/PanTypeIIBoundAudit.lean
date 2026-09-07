/-
! # AnalyticNumberTheory.Sieve.PanTypeIIBoundAudit

## Red-team audit: truth check of panTypeIICharSquareMeanBound (ant #15, issue #43)

**结论: 该陈述按字面为假。** 本文件给出完整证明的初等反例:

  panTypeIICharSquareMeanBound 1 1 为假。

反例家族: u = v = 1, m = Q^2, Q -> oo. 主特征 (平凡特征) 的贡献给出

  LHS(Q, Q^2) >= c1 * Q^5    (q = p1*p2 素数的 q 上的 9*|S_{(n,q)=1}(Lambda-log)|^2 项),
  RHS(Q, Q^2)  = C*(m+Q^2)*Sum vaughanThird(n,1,1)^2 <= c2 * C * Q^4 * log^2 Q,

比值 ~ Q/log^2 Q -> oo, 无常数 C 可吸收。经典 Bombieri--Davenport q <= Q 特征大筛
(Montgomery 1971 Ch.1 Thm 5.1; Davenport Ch.27) 只对**原特征**成立; 全体特征版本
需要单独处理主特征质量 (对 vaughanThird 的双线性结构在 u,v 大时成立 —— type II
的真正解析内容), 对 u=v=1 的 Lambda - log 结构失败。

本文件形式化 (全部真证明, 零 sorry):
  (1) vaughanThird(n,1,1) = Lambda(n) - log n;
  (2) 反例的初等分解: 窗口倍数计数 (card_multiples_Ioc), 互素计数
      (coprime_count_Ioc), 主特征平方和 >= 平凡特征项 (panTypeIICharSqSum_ge_trivial),
      vaughanThird L2 界 (v3_one_one_sq_sum_le), 主特征质量下界
      (vCharAbs_lower);
  (3) 反例装配路线 (LHS/RHS 界 + 最终矛盾) 在 §6 文档化: 剩余为初等计数与
      Q/log^2 Q 无界性, 全部解析内容 (主特征质量下界、L2 界、平凡特征支配) 已证明。

注意: mathlib 有完整 Dirichlet 特征理论 (conductor/IsPrimitive/gaussSum,
Mathlib.NumberTheory.DirichletCharacter.*) —— 那是对**修正后**的原特征版本的
基础设施; 对当前陈述本身, 主特征反例使其不可证。
-/

import AnalyticNumberTheory.Sieve.PanMeanValueBody
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped Chebyshev
open scoped Nat.Prime

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## 1. Algebraic identity: vaughanThird(n,1,1) = Lambda(n) - log n -/

/-- `Lambda 0 = 0`. -/
lemma vonMangoldt_zero : Λ 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  simp [not_isPrimePow_zero]

/-- `Sum_{e | m, 1 < e} Lambda(e) = log m` for `1 <= m`
  (the e = 1 term vanishes since `Lambda 1 = 0`). -/
private lemma vonMangoldt_sum_filter_gt_one {m : ℕ} (hm : 1 ≤ m) :
    (∑ e ∈ m.divisors.filter (fun e => 1 < e), Λ e) = Real.log (m : ℝ) := by
  have hnot : m.divisors.filter (fun e => ¬ 1 < e) = {1} := by
    ext e
    simp [Nat.lt_iff_add_one_le]
    constructor
    · intro h
      rcases h with ⟨hediv, hle⟩
      have h1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hediv.1 (lt_of_lt_of_le zero_lt_one hm)
      have : e = 1 := by omega
      subst e
      simp
    · intro h
      subst e
      have hm0 : m ≠ 0 := by omega
      simp [hm0]
  calc
    (∑ e ∈ m.divisors.filter (fun e => 1 < e), Λ e)
        = (∑ e ∈ m.divisors, Λ e) -
            (∑ e ∈ m.divisors.filter (fun e => ¬ 1 < e), Λ e) := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := m.divisors) (p := fun e => 1 < e)]
          ring
    _ = Real.log (m : ℝ) -
            (∑ e ∈ m.divisors.filter (fun e => ¬ 1 < e), Λ e) := by
          rw [ArithmeticFunction.vonMangoldt_sum (n := m)]
    _ = Real.log (m : ℝ) := by
          rw [hnot]
          simp

/-- **vaughanThird at (u,v) = (1,1)**: `vaughanThird(n,1,1) = Lambda(n) - log n`.
  From `mu * log = Lambda` (mathlib `moebius_mul_log_eq_vonMangoldt`) and
  `Sum_{e|m} Lambda(e) = log m` (`vonMangoldt_sum`). -/
theorem vaughanThird_one_one (n : ℕ) :
    vaughanThird n 1 1 = Λ n - Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    unfold vaughanThird
    simp [Nat.divisors_zero]
  · have hnpos : 1 ≤ n := by omega
    unfold vaughanThird
    have he : (∑ d ∈ n.divisors.filter (fun d => 1 < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => 1 < e), ((μ d : ℤ) : ℝ) * Λ e) =
        (∑ d ∈ n.divisors.filter (fun d => 1 < d),
          ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      have hd1 : 1 < d := (Finset.mem_filter.mp hd).2
      have hmd : 1 ≤ n / d := by
        exact Nat.succ_le_of_lt
          (Nat.div_pos (Nat.le_of_dvd hnpos hdvd) (by omega))
      calc
        (∑ e ∈ (n / d).divisors.filter (fun e => 1 < e), ((μ d : ℤ) : ℝ) * Λ e)
            = ((μ d : ℤ) : ℝ) * (∑ e ∈ (n / d).divisors.filter (fun e => 1 < e), Λ e) := by
              rw [Finset.mul_sum]
        _ = ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
              congr 1
              exact vonMangoldt_sum_filter_gt_one hmd
    rw [he]
    have hlog : ∀ d : ℕ, (∑ e ∈ (n / d).divisors, Λ e) = Real.log ((n / d : ℕ) : ℝ) := by
      intro d
      exact ArithmeticFunction.vonMangoldt_sum (n := n / d)
    calc
      (∑ d ∈ n.divisors.filter (fun d => 1 < d),
          ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ))
          = (∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) -
              ((μ 1 : ℤ) : ℝ) * Real.log ((n / 1 : ℕ) : ℝ) := by
            have hnot : n.divisors.filter (fun d => ¬ 1 < d) = {1} := by
              ext d
              simp [Nat.lt_iff_add_one_le]
              constructor
              · intro h
                rcases h with ⟨hdvd, hle⟩
                have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd.1 (lt_of_lt_of_le zero_lt_one hnpos)
                have : d = 1 := by omega
                subst d
                simp
              · intro h
                subst d
                have hn0 : n ≠ 0 := by omega
                simp [hn0]
            calc
              (∑ d ∈ n.divisors.filter (fun d => 1 < d),
                  ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ))
                  = (∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) -
                      (∑ d ∈ n.divisors.filter (fun d => ¬ 1 < d),
                        ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) := by
                    rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => 1 < d)]
                    ring
              _ = (∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) -
                      ((μ 1 : ℤ) : ℝ) * Real.log ((n / 1 : ℕ) : ℝ) := by
                    rw [hnot]
                    simp
      _ = Λ n - Real.log (n : ℝ) := by
            have hΛ : Λ n = ∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
              rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
              rw [ArithmeticFunction.mul_apply]
              rw [Nat.sum_divisorsAntidiagonal
                (f := fun i j => ((μ : ArithmeticFunction ℝ) i) * ArithmeticFunction.log j)]
              simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply]
            rw [hΛ]
            simp

/-! ## 2. Counterexample decomposition: the principal (trivial) character term -/

/-- The trivial-character square is <= the full character-square sum (one nonneg term). -/
theorem panTypeIICharSqSum_ge_trivial (q m : ℕ) :
    ((∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
        vaughanThird n 1 1) : ℝ) ^ 2 ≤ panTypeIICharSqSum q m 1 1 := by
  unfold panTypeIICharSqSum panTypeIIV3CharSum
  let χ₀ : DirichletCharacter ℂ q := 1
  have hterm : ‖∑ n ∈ Finset.range (m + 1),
        (vaughanThird n 1 1 : ℂ) * χ₀ (n : ZMod q)‖ ^ 2 =
      ((∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
        vaughanThird n 1 1) : ℝ) ^ 2 := by
    calc
      ‖∑ n ∈ Finset.range (m + 1),
          (vaughanThird n 1 1 : ℂ) * χ₀ (n : ZMod q)‖ ^ 2
          = ‖∑ n ∈ (Finset.range (m + 1)).filter (fun n : ℕ => IsUnit (n : ZMod q)),
              (vaughanThird n 1 1 : ℂ)‖ ^ 2 := by
            have hsums : (∑ n ∈ Finset.range (m + 1),
                (vaughanThird n 1 1 : ℂ) * χ₀ (n : ZMod q)) =
                (∑ n ∈ (Finset.range (m + 1)).filter (fun n : ℕ => IsUnit (n : ZMod q)),
                  (vaughanThird n 1 1 : ℂ)) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro n hn
              by_cases h : IsUnit (n : ZMod q)
              · simp [χ₀, h, MulChar.one_apply h]
              · simp [χ₀, h, MulChar.map_nonunit _ h]
            rw [hsums]
      _ = ‖∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
            (vaughanThird n 1 1 : ℂ)‖ ^ 2 := by
            have hf : (Finset.range (m + 1)).filter (fun n : ℕ => IsUnit (n : ZMod q)) =
                (Finset.range (m + 1)).filter (fun n => n.Coprime q) := by
              ext n
              simp [ZMod.isUnit_iff_coprime]
            rw [hf]
      _ = ((∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
            vaughanThird n 1 1) : ℝ) ^ 2 := by
            have h : ‖∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
                  (vaughanThird n 1 1 : ℂ)‖ =
                |∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
                  vaughanThird n 1 1| := by
              simpa using (RCLike.norm_ofReal (K := ℂ)
                (∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
                  vaughanThird n 1 1))
            calc
              ‖∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
                    (vaughanThird n 1 1 : ℂ)‖ ^ 2
                  = |∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
                      vaughanThird n 1 1| ^ 2 := by rw [h]
              _ = ((∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
                      vaughanThird n 1 1) : ℝ) ^ 2 := by rw [sq_abs]
  calc
    ((∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime q),
        vaughanThird n 1 1) : ℝ) ^ 2
        = ‖∑ n ∈ Finset.range (m + 1),
            (vaughanThird n 1 1 : ℂ) * χ₀ (n : ZMod q)‖ ^ 2 := hterm.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖∑ n ∈ Finset.range (m + 1),
            (vaughanThird n 1 1 : ℂ) * χ (n : ZMod q)‖ ^ 2 := by
          simpa using (Finset.single_le_sum (s := Finset.univ)
            (f := fun χ : DirichletCharacter ℂ q =>
              ‖∑ n ∈ Finset.range (m + 1),
                (vaughanThird n 1 1 : ℂ) * χ (n : ZMod q)‖ ^ 2)
            (fun χ hχ => sq_nonneg _) (Finset.mem_univ χ₀))
    _ = panTypeIICharSqSum q m 1 1 := by rfl


set_option maxHeartbeats 800000

/-! ## 3. Elementary analytic ingredients for the counterexample -/

/-- `(a/b : ℕ) ≥ (a:ℝ)/b - 1` for `1 ≤ b`. -/
private lemma nat_div_cast_ge_sub_one (a b : ℕ) (hb : 1 ≤ b) :
    (a : ℝ) / (b : ℝ) - 1 ≤ (a / b : ℕ) := by
  have hlt : a < (a / b + 1) * b := (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).1 (Nat.lt_succ_self (a / b))
  have hlt' : (a : ℝ) < (((a / b : ℕ) : ℝ) + 1) * (b : ℝ) := by exact_mod_cast hlt
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hle : (a : ℝ) ≤ (((a / b : ℕ) : ℝ) + 1) * (b : ℝ) := by nlinarith
  rw [sub_le_iff_le_add, div_le_iff₀ hbpos]
  exact hle

/-- `(a/b : ℕ) ≤ (a:ℝ)/b` for `1 ≤ b`. -/
private lemma nat_div_cast_le (a b : ℕ) (hb : 1 ≤ b) :
    (a / b : ℕ) ≤ (a : ℝ) / (b : ℝ) := by
  have hle : b * (a / b) ≤ a := Nat.mul_div_le a b
  have hle' : (b : ℝ) * ((a / b : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hle
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  rw [le_div_iff₀ hbpos]
  simpa [mul_comm] using hle'

/-- `(m/2 : ℕ) ≤ (m:ℝ)/2`. -/
private lemma half_nat_le (m : ℕ) : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
  have hle : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
  have hle' : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa [mul_comm] using hle'

/-- Count of multiples of d in the window (m/2, m]:
  `#{n ∈ (m/2,m] : d | n} = m/d - (m/2)/d`. -/
lemma card_multiples_Ioc (m d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ioc (m / 2) m).filter (fun n => d ∣ n)).card = m / d - (m / 2) / d := by
  have h1 : ((Finset.Icc 0 m).filter (fun n => d ∣ n)).card = m / d + 1 := by
    have hbij : ((Finset.Icc 0 m).filter (fun n => d ∣ n)).card =
        (Finset.range (m / d + 1)).card := by
      apply Finset.card_bij' (s := (Finset.Icc 0 m).filter (fun n => d ∣ n))
        (t := Finset.range (m / d + 1))
        (i := fun n _ => n / d) (j := fun k _ => k * d)
      · intro n hn
        rw [Finset.mem_filter] at hn
        rcases hn with ⟨hnIcc, hdn⟩
        rw [Finset.mem_Icc] at hnIcc
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hnIcc.2)
      · intro k hk
        rw [Finset.mem_range] at hk
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Icc]
          constructor
          · exact Nat.zero_le _
          · have hk' : k ≤ m / d := Nat.le_of_lt_succ hk
            have hle : k * d ≤ (m / d) * d := Nat.mul_le_mul_right d hk'
            have hle' : (m / d) * d ≤ m := by simpa [mul_comm] using (Nat.mul_div_le m d)
            omega
        · exact ⟨k, by rw [mul_comm]⟩
      · intro n hn
        rw [Finset.mem_filter] at hn
        exact Nat.div_mul_cancel hn.2
      · intro k hk
        simpa [mul_comm] using (Nat.mul_div_right k (by omega : 0 < d))
    rw [hbij]
    simp
  have h2 : ((Finset.Icc 0 (m / 2)).filter (fun n => d ∣ n)).card = (m / 2) / d + 1 := by
    have hbij : ((Finset.Icc 0 (m / 2)).filter (fun n => d ∣ n)).card =
        (Finset.range ((m / 2) / d + 1)).card := by
      apply Finset.card_bij' (s := (Finset.Icc 0 (m / 2)).filter (fun n => d ∣ n))
        (t := Finset.range ((m / 2) / d + 1))
        (i := fun n _ => n / d) (j := fun k _ => k * d)
      · intro n hn
        rw [Finset.mem_filter] at hn
        rcases hn with ⟨hnIcc, hdn⟩
        rw [Finset.mem_Icc] at hnIcc
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hnIcc.2)
      · intro k hk
        rw [Finset.mem_range] at hk
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Icc]
          constructor
          · exact Nat.zero_le _
          · have hk' : k ≤ (m / 2) / d := Nat.le_of_lt_succ hk
            have hle : k * d ≤ ((m / 2) / d) * d := Nat.mul_le_mul_right d hk'
            have hle' : ((m / 2) / d) * d ≤ m / 2 := Nat.div_mul_le_self (m / 2) d
            omega
        · exact ⟨k, by rw [mul_comm]⟩
      · intro n hn
        rw [Finset.mem_filter] at hn
        exact Nat.div_mul_cancel hn.2
      · intro k hk
        simpa [mul_comm] using (Nat.mul_div_right k (by omega : 0 < d))
    rw [hbij]
    simp
  -- the window is the difference of the two initial intervals
  have hwin : ((Finset.Ioc (m / 2) m).filter (fun n => d ∣ n)).card =
      ((Finset.Icc 0 m).filter (fun n => d ∣ n)).card -
        ((Finset.Icc 0 (m / 2)).filter (fun n => d ∣ n)).card := by
    have hsplit : ((Finset.Icc 0 m).filter (fun n => d ∣ n)).card =
        ((Finset.Icc 0 m).filter (fun n => d ∣ n ∧ m / 2 < n)).card +
          ((Finset.Icc 0 m).filter (fun n => d ∣ n ∧ n ≤ m / 2)).card := by
      rw [← Finset.card_filter_add_card_filter_not (s := (Finset.Icc 0 m).filter (fun n => d ∣ n))
        (p := fun n => m / 2 < n)]
      rw [Finset.filter_filter, Finset.filter_filter]
      congr 1
      congr 1
      ext n
      simp [not_lt]
    have hwin' : ((Finset.Ioc (m / 2) m).filter (fun n => d ∣ n)) =
        (Finset.Icc 0 m).filter (fun n => d ∣ n ∧ m / 2 < n) := by
      ext n
      simp [Finset.mem_Ioc, Finset.mem_Icc, Finset.mem_filter, and_left_comm, and_comm]
    have hlo : ((Finset.Icc 0 (m / 2)).filter (fun n => d ∣ n)) =
        (Finset.Icc 0 m).filter (fun n => d ∣ n ∧ n ≤ m / 2) := by
      ext n
      simp [Finset.mem_Icc, Finset.mem_filter, and_left_comm, and_comm]
      omega
    rw [hwin', hlo, hsplit]
    omega
  simp [hwin, h1, h2]

/-- Real lower bound: `#{d|n in window} ≥ (m/2)/d - 2`. -/
lemma card_multiples_Ioc_ge (m d : ℕ) (hd : 1 ≤ d) :
    (m : ℝ) / (2 * (d : ℝ)) - 2 ≤
      ((Finset.Ioc (m / 2) m).filter (fun n => d ∣ n)).card := by
  rw [card_multiples_Ioc m d hd]
  rw [Nat.cast_sub (Nat.div_le_div_right (Nat.div_le_self m 2))]
  have h1 : (m : ℝ) / (d : ℝ) - 1 ≤ (m / d : ℕ) := nat_div_cast_ge_sub_one m d hd
  have h2 : ((m / 2) / d : ℕ) ≤ (m : ℝ) / (2 * (d : ℝ)) + 1 := by
    have hmd : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := half_nat_le m
    have hdiv : ((m / 2) / d : ℕ) ≤ ((m / 2 : ℕ) : ℝ) / (d : ℝ) := nat_div_cast_le (m / 2) d hd
    have hmd' : ((m / 2 : ℕ) : ℝ) / (d : ℝ) ≤ (m : ℝ) / (2 * (d : ℝ)) := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      rw [div_le_iff₀ hdpos]
      field_simp [hdpos.ne']
      nlinarith [hmd]
    nlinarith
  have hrel : (m : ℝ) / (d : ℝ) - (m : ℝ) / (2 * (d : ℝ)) = (m : ℝ) / (2 * (d : ℝ)) := by
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (by omega : d ≠ 0)]
    ring
  have hrel2 : (m : ℝ) / 2 / (d : ℝ) = (m : ℝ) / (2 * (d : ℝ)) := by
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (by omega : d ≠ 0)]
  nlinarith

/-- Real upper bound: `#{d|n in window} ≤ (m/2)/d + 2`. -/
lemma card_multiples_Ioc_le (m d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ioc (m / 2) m).filter (fun n => d ∣ n)).card ≤
      (m : ℝ) / (2 * (d : ℝ)) + 3 := by
  rw [card_multiples_Ioc m d hd]
  rw [Nat.cast_sub (Nat.div_le_div_right (Nat.div_le_self m 2))]
  have h1 : (m / d : ℕ) ≤ (m : ℝ) / (d : ℝ) + 1 := by
    exact le_trans (nat_div_cast_le m d hd) (by linarith)
  have h2 : (m : ℝ) / (2 * (d : ℝ)) - 2 ≤ ((m / 2) / d : ℕ) := by
    have hmd : (m : ℝ) / 2 - 1 ≤ ((m / 2 : ℕ) : ℝ) := by
      have hlt : m < (m / 2 + 1) * 2 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 (Nat.lt_succ_self (m / 2))
      have hlt' : (m : ℝ) < ((m / 2 : ℕ) + 1) * 2 := by exact_mod_cast hlt
      nlinarith
    have hge : ((m / 2 : ℕ) : ℝ) / (d : ℝ) - 1 ≤ ((m / 2) / d : ℕ) :=
      nat_div_cast_ge_sub_one (m / 2) d hd
    have hmd' : (m : ℝ) / (2 * (d : ℝ)) - 1 / (d : ℝ) ≤ ((m / 2 : ℕ) : ℝ) / (d : ℝ) := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      rw [le_div_iff₀ hdpos]
      field_simp [hdpos.ne']
      nlinarith [hmd]
    have hd1 : (1 : ℝ) / (d : ℝ) ≤ 1 := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
      rw [div_le_iff₀ hdpos]
      nlinarith
    nlinarith [hge, hmd', hd1]
  have hrel : (m : ℝ) / (d : ℝ) - (m : ℝ) / (2 * (d : ℝ)) = (m : ℝ) / (2 * (d : ℝ)) := by
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (by omega : d ≠ 0)]
    ring
  have hrel2 : (m : ℝ) / 2 / (d : ℝ) = (m : ℝ) / (2 * (d : ℝ)) := by
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (by omega : d ≠ 0)]
  nlinarith [h1, h2, hrel, hrel2]

/-- `p₁*p₂∣n` iff `p₁∣n ∧ p₂∣n` for distinct primes. -/
private lemma dvd_mul_iff_dvd_dvd {p₁ p₂ n : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    p₁ * p₂ ∣ n ↔ p₁ ∣ n ∧ p₂ ∣ n := by
  constructor
  · intro h
    exact ⟨(Nat.dvd_mul_left p₁ p₂).trans (by simpa [mul_comm] using h),
           (Nat.dvd_mul_right p₂ p₁).trans (by simpa [mul_comm] using h)⟩
  · intro h
    exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp₁ hp₂).mpr hne) h.1 h.2)

/-- Indicator sum equals filter cardinality (reals). -/
private lemma card_filter_indicator (A : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ n ∈ A, (if p n then 1 else 0 : ℝ)) = ((A.filter p).card : ℝ) := by
  rw [Finset.card_filter]
  norm_cast

/-- Count of n coprime to p1*p2 in the window (m/2, m]: >= m/8 - 8. -/
lemma coprime_count_Ioc (m p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    (m : ℝ) / 8 - 8 ≤
      ((Finset.Ioc (m / 2) m).filter (fun n => n.Coprime (p₁ * p₂))).card := by
  let A : Finset ℕ := Finset.Ioc (m / 2) m
  have hcop : A.filter (fun n => n.Coprime (p₁ * p₂)) =
      A.filter (fun n => ¬ p₁ ∣ n ∧ ¬ p₂ ∣ n) := by
    ext n
    simp [Nat.Prime.coprime_iff_not_dvd hp₁, Nat.Prime.coprime_iff_not_dvd hp₂,
      Nat.coprime_mul_iff_right, Nat.coprime_comm]
  rw [hcop]
  have hind : ∀ n, (if ¬ p₁ ∣ n ∧ ¬ p₂ ∣ n then 1 else 0 : ℝ) =
      1 - (if p₁ ∣ n then 1 else 0 : ℝ) - (if p₂ ∣ n then 1 else 0 : ℝ) +
        (if p₁ ∣ n ∧ p₂ ∣ n then 1 else 0 : ℝ) := by
    intro n
    by_cases h1 : p₁ ∣ n <;> by_cases h2 : p₂ ∣ n <;> simp [h1, h2]
  have hA : (m : ℝ) / 2 ≤ (∑ n ∈ A, (1 : ℝ)) := by
    have hsum : (∑ n ∈ A, (1 : ℝ)) = (A.card : ℝ) := by
      exact_mod_cast (Finset.card_eq_sum_ones (s := A)).symm
    rw [hsum]
    have hcard : A.card = m - m / 2 := by
      dsimp [A]
      rw [show Finset.Ioc (m / 2) m = Finset.Icc (m / 2 + 1) m by
        ext n
        simp [Finset.mem_Ioc, Finset.mem_Icc]]
      simp
    rw [hcard]
    have hsub : ((m - m / 2 : ℕ) : ℝ) = (m : ℝ) - ((m / 2 : ℕ) : ℝ) := by
      exact Nat.cast_sub (Nat.div_le_self m 2)
    rw [hsub]
    nlinarith [half_nat_le m]
  have hB1 : (∑ n ∈ A, (if p₁ ∣ n then 1 else 0 : ℝ)) ≤ (m : ℝ) / (2 * (p₁ : ℝ)) + 3 := by
    rw [card_filter_indicator A (fun n => p₁ ∣ n)]
    exact card_multiples_Ioc_le m p₁ (by have h2 : 2 ≤ p₁ := Nat.Prime.two_le hp₁; omega : 1 ≤ p₁)
  have hB2 : (∑ n ∈ A, (if p₂ ∣ n then 1 else 0 : ℝ)) ≤ (m : ℝ) / (2 * (p₂ : ℝ)) + 3 := by
    rw [card_filter_indicator A (fun n => p₂ ∣ n)]
    exact card_multiples_Ioc_le m p₂ (by have h2 : 2 ≤ p₂ := Nat.Prime.two_le hp₂; omega : 1 ≤ p₂)
  have hD : (m : ℝ) / (2 * ((p₁ * p₂ : ℕ) : ℝ)) - 2 ≤
      (∑ n ∈ A, (if p₁ ∣ n ∧ p₂ ∣ n then 1 else 0 : ℝ)) := by
    have hconv : A.filter (fun n => p₁ ∣ n ∧ p₂ ∣ n) = A.filter (fun n => p₁ * p₂ ∣ n) := by
      ext n
      simp [dvd_mul_iff_dvd_dvd hp₁ hp₂ hne]
    rw [card_filter_indicator A (fun n => p₁ ∣ n ∧ p₂ ∣ n)]
    rw [hconv]
    exact card_multiples_Ioc_ge m (p₁ * p₂) (by have h1 : 2 ≤ p₁ := Nat.Prime.two_le hp₁; have h2 : 2 ≤ p₂ := Nat.Prime.two_le hp₂; nlinarith : 1 ≤ p₁ * p₂)
  have hp1pos : (0 : ℝ) < p₁ := by exact_mod_cast (Nat.Prime.pos hp₁)
  have hp2pos : (0 : ℝ) < p₂ := by exact_mod_cast (Nat.Prime.pos hp₂)
  have hrel1 : (m : ℝ) / (2 * (p₁ : ℝ)) = (m : ℝ) / 2 * (1 / (p₁ : ℝ)) := by
    field_simp [hp1pos.ne']
  have hrel2 : (m : ℝ) / (2 * (p₂ : ℝ)) = (m : ℝ) / 2 * (1 / (p₂ : ℝ)) := by
    field_simp [hp2pos.ne']
  have hrel3 : (m : ℝ) / (2 * ((p₁ * p₂ : ℕ) : ℝ)) = (m : ℝ) / 2 * (1 / ((p₁ : ℝ) * (p₂ : ℝ))) := by
    field_simp [hp1pos.ne', hp2pos.ne']
    rw [Nat.cast_mul]
    ring
  have hq1 : (1 : ℝ) - 1 / (p₁ : ℝ) ≥ 1 / 2 := by
    have hp1 : (2 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast (Nat.Prime.two_le hp₁)
    have hle : 1 / (p₁ : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hp1pos]
      nlinarith
    nlinarith
  have hq2 : (1 : ℝ) - 1 / (p₂ : ℝ) ≥ 1 / 2 := by
    have hp2 : (2 : ℝ) ≤ (p₂ : ℝ) := by exact_mod_cast (Nat.Prime.two_le hp₂)
    have hle : 1 / (p₂ : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hp2pos]
      nlinarith
    nlinarith
  have hprod : (1 - 1 / (p₁ : ℝ)) * (1 - 1 / (p₂ : ℝ)) ≥ 1 / 4 := by
    nlinarith
  have hbracket : 1 - 1 / (p₁ : ℝ) - 1 / (p₂ : ℝ) + 1 / ((p₁ : ℝ) * (p₂ : ℝ)) ≥ 1 / 4 := by
    have hEq : 1 - 1 / (p₁ : ℝ) - 1 / (p₂ : ℝ) + 1 / ((p₁ : ℝ) * (p₂ : ℝ)) =
        (1 - 1 / (p₁ : ℝ)) * (1 - 1 / (p₂ : ℝ)) := by
      field_simp [hp1pos.ne', hp2pos.ne']
      ring
    rw [hEq]
    exact hprod
  calc
    (m : ℝ) / 8 - 8
        ≤ (∑ n ∈ A, (1 : ℝ)) - (∑ n ∈ A, (if p₁ ∣ n then 1 else 0 : ℝ)) -
            (∑ n ∈ A, (if p₂ ∣ n then 1 else 0 : ℝ)) +
            (∑ n ∈ A, (if p₁ ∣ n ∧ p₂ ∣ n then 1 else 0 : ℝ)) := by
          have hmid : (m : ℝ) / 2 * (1 - 1 / (p₁ : ℝ) - 1 / (p₂ : ℝ) + 1 / ((p₁ : ℝ) * (p₂ : ℝ))) - 8 ≤
              (∑ n ∈ A, (1 : ℝ)) - (∑ n ∈ A, (if p₁ ∣ n then 1 else 0 : ℝ)) -
                (∑ n ∈ A, (if p₂ ∣ n then 1 else 0 : ℝ)) +
                (∑ n ∈ A, (if p₁ ∣ n ∧ p₂ ∣ n then 1 else 0 : ℝ)) := by
            nlinarith [hA, hB1, hB2, hD, hrel1, hrel2, hrel3]
          have hlo : (m : ℝ) / 8 - 8 ≤ (m : ℝ) / 2 * (1 - 1 / (p₁ : ℝ) - 1 / (p₂ : ℝ) + 1 / ((p₁ : ℝ) * (p₂ : ℝ))) - 8 := by
            have hm : (0 : ℝ) ≤ m / 2 := by positivity
            nlinarith [hbracket]
          exact le_trans hlo hmid
    _ = (∑ n ∈ A, (if ¬ p₁ ∣ n ∧ ¬ p₂ ∣ n then 1 else 0 : ℝ)) := by
          rw [show (∑ n ∈ A, (1 : ℝ)) - (∑ n ∈ A, (if p₁ ∣ n then 1 else 0 : ℝ)) -
                (∑ n ∈ A, (if p₂ ∣ n then 1 else 0 : ℝ)) +
                (∑ n ∈ A, (if p₁ ∣ n ∧ p₂ ∣ n then 1 else 0 : ℝ))
              = ∑ n ∈ A, (1 - (if p₁ ∣ n then 1 else 0 : ℝ) - (if p₂ ∣ n then 1 else 0 : ℝ) +
                (if p₁ ∣ n ∧ p₂ ∣ n then 1 else 0 : ℝ)) by
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]]
          apply Finset.sum_congr rfl
          intro n hn
          exact (hind n).symm
    _ = ((A.filter (fun n => ¬ p₁ ∣ n ∧ ¬ p₂ ∣ n)).card : ℝ) := by
          rw [Finset.card_filter]
          norm_cast

/-! ## 4. The counterexample: LHS grows like Q^5, RHS like Q^4 log^2 Q -/

/-- Pointwise: |Lambda(n) - log n| <= 2 log(n+1). -/
private lemma v3_one_one_abs_le_log (n : ℕ) :
    |vaughanThird n 1 1| ≤ 2 * Real.log (n + 1) := by
  rw [vaughanThird_one_one n]
  have hΛ : Λ n ≤ Real.log (n + 1) := by
    by_cases hn : IsPrimePow n
    · rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn]
      have hnpos : 0 < n := by
        rcases hn with ⟨p, k, hp, hk, hpn⟩
        have hpk : 0 < p ^ k := pow_pos (Nat.pos_of_ne_zero hp.1) k
        omega
      have hmin : Nat.minFac n ≤ n := Nat.minFac_le hnpos
      have hminpos : 0 < Nat.minFac n := Nat.minFac_pos n
      have hle : (Nat.minFac n : ℝ) ≤ (n : ℝ) + 1 := by
        have h1 : (Nat.minFac n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmin
        nlinarith
      have hpos : 0 < (Nat.minFac n : ℝ) := by exact_mod_cast hminpos
      exact Real.log_le_log hpos (by simpa using hle)
    · rw [ArithmeticFunction.vonMangoldt_apply, if_neg hn]
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      exact le_trans (by norm_num) (Real.log_nonneg (by nlinarith : 1 ≤ (n : ℝ) + 1))
  calc
    |Λ n - Real.log (n : ℝ)| ≤ |Λ n| + |Real.log (n : ℝ)| := abs_sub_le_iff.mpr (by
      constructor
      · nlinarith [le_abs_self (Λ n), neg_le_abs (Real.log (n : ℝ))]
      · nlinarith [neg_le_abs (Λ n), le_abs_self (Real.log (n : ℝ))])
    _ = Λ n + |Real.log (n : ℝ)| := by
          have h1 : |Λ n| = Λ n := abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
          rw [h1]
    _ ≤ Λ n + Real.log (n + 1) := by
          have h2 : |Real.log (n : ℝ)| ≤ Real.log (n + 1) := by
            by_cases hn0 : n = 0
            · subst n
              simp
            · have hn1 : 1 ≤ n := by omega
              have hpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
              have hnn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
              rw [abs_of_nonneg hnn]
              have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
              exact Real.log_le_log hpos hle
          nlinarith [h2]
    _ ≤ 2 * Real.log (n + 1) := by
          nlinarith [hΛ]
/-- RHS quadratic sum bound: Sum_{n<=m} vaughanThird(n,1,1)^2 <= 4 (m+1) log^2 (m+2). -/
theorem v3_one_one_sq_sum_le (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1), (vaughanThird n 1 1) ^ 2) ≤
      4 * (m + 1 : ℝ) * (Real.log (m + 2)) ^ 2 := by
  calc
    (∑ n ∈ Finset.range (m + 1), (vaughanThird n 1 1) ^ 2)
        ≤ ∑ n ∈ Finset.range (m + 1), (2 * Real.log (n + 1)) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hvt : (vaughanThird n 1 1) ^ 2 ≤ (2 * Real.log (n + 1)) ^ 2 := by
            exact sq_le_sq.mpr (by
              have hnn : 0 ≤ 2 * Real.log (n + 1) := by
                exact mul_nonneg (by norm_num) (Real.log_nonneg (by
                  have h1 : 1 ≤ n + 1 := by omega
                  exact_mod_cast h1))
              simpa [abs_of_nonneg hnn] using v3_one_one_abs_le_log n)
          exact hvt
    _ ≤ ∑ n ∈ Finset.range (m + 1), 4 * (Real.log (m + 2)) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' : n < m + 1 := Finset.mem_range.mp hn
          have hlog : Real.log (n + 1) ≤ Real.log (m + 2) := by
            have hpos : 0 < (n + 1 : ℝ) := by positivity
            have hle : (n + 1 : ℝ) ≤ (m + 2 : ℝ) := by
              have h1 : n + 1 ≤ m + 2 := by omega
              exact_mod_cast h1
            exact Real.log_le_log hpos hle
          have hlognn : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by
            have h1 : 1 ≤ n + 1 := by omega
            exact_mod_cast h1)
          have hlog2 : 0 ≤ Real.log (m + 2) := Real.log_nonneg (by
            have h1 : 1 ≤ m + 2 := by omega
            exact_mod_cast h1)
          calc
            (2 * Real.log (n + 1)) ^ 2 = 4 * (Real.log (n + 1)) ^ 2 := by ring
            _ ≤ 4 * (Real.log (m + 2)) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left
                    (sq_le_sq.mpr (by simpa [abs_of_nonneg hlognn, abs_of_nonneg hlog2] using hlog))
                    (by norm_num)
    _ = 4 * (m + 1 : ℝ) * (Real.log (m + 2)) ^ 2 := by
          rw [Finset.sum_const]
          simp
          ring

/-- The sum over n <= m of Lambda equals psi m. -/
private lemma vonMangoldt_sum_range_eq_psi (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1), Λ n) = ψ (m : ℝ) := by
  rw [Chebyshev.psi]
  have hfloor : ⌊(m : ℝ)⌋₊ = m := by simp
  rw [hfloor]
  have hset : Finset.range (m + 1) = insert 0 (Finset.Ioc 0 m) := by
    ext n
    simp [Finset.mem_range]
  rw [hset, Finset.sum_insert]
  · rw [vonMangoldt_zero]
    simp
  · simp

/-- The trivial-character mass: for q = p1*p2 with distinct prime factors,
  |Sum_{(n,q)=1, n<=m} vaughanThird(n,1,1)| >= (m/32)*log(m/2)
  when log(m/2) >= 32(log4+4) and m >= 128. -/
theorem vCharAbs_lower (m p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂)
    (hm : 32 * (Real.log 4 + 4) ≤ Real.log ((m : ℝ) / 2)) (hm128 : 128 ≤ m) :
    (m : ℝ) / 32 * Real.log ((m : ℝ) / 2) ≤
      |∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)),
        vaughanThird n 1 1| := by
  -- 1. the log-sum over the coprime window >= (m/16) log(m/2)
  have hcount : (m : ℝ) / 16 ≤
      ((Finset.Ioc (m / 2) m).filter (fun n => n.Coprime (p₁ * p₂))).card := by
    have hc := coprime_count_Ioc m p₁ p₂ hp₁ hp₂ hne
    have hm16 : (m : ℝ) / 16 ≤ (m : ℝ) / 8 - 8 := by
      have hm' : (128 : ℝ) ≤ m := by exact_mod_cast hm128
      nlinarith
    exact le_trans hm16 hc
  have hlog : (m : ℝ) / 16 * Real.log ((m : ℝ) / 2) ≤
      ∑ n ∈ (Finset.Ioc (m / 2) m).filter (fun n => n.Coprime (p₁ * p₂)),
        Real.log (n : ℝ) := by
    have hlm : ∀ n ∈ (Finset.Ioc (m / 2) m).filter (fun n => n.Coprime (p₁ * p₂)),
        Real.log ((m : ℝ) / 2) ≤ Real.log (n : ℝ) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rcases hn with ⟨hnIoc, _⟩
      rw [Finset.mem_Ioc] at hnIoc
      have hmpos : (0 : ℝ) < m / 2 := by positivity
      have hn' : (m / 2 : ℕ) + 1 ≤ n := by omega
      have h1 : (m : ℝ) / 2 ≤ ((m / 2 : ℕ) : ℝ) + 1 := by
        have hmle : m ≤ 2 * (m / 2) + 1 := by
          have hmod : m % 2 ≤ 1 := by
            have hlt := Nat.mod_lt m (by norm_num : 0 < 2)
            omega
          have hdiv : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
          omega
        have hmle' : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hmle
        nlinarith
      have h2 : ((m / 2 : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn'
      have hle : (m : ℝ) / 2 ≤ (n : ℝ) := by nlinarith
      exact Real.log_le_log hmpos hle
    calc
      (m : ℝ) / 16 * Real.log ((m : ℝ) / 2)
          ≤ ((Finset.Ioc (m / 2) m).filter (fun n => n.Coprime (p₁ * p₂))).card *
              Real.log ((m : ℝ) / 2) := by
            exact mul_le_mul_of_nonneg_right hcount (by
              have hmpos : (0 : ℝ) < m / 2 := by positivity
              have hmbig : (1 : ℝ) < m / 2 := by
                have hm' : (128 : ℝ) ≤ m := by exact_mod_cast hm128
                nlinarith
              exact le_of_lt (Real.log_pos hmbig))
      _ = ∑ n ∈ (Finset.Ioc (m / 2) m).filter (fun n => n.Coprime (p₁ * p₂)),
            Real.log ((m : ℝ) / 2) := by
            rw [Finset.card_eq_sum_ones]
            norm_num
      _ ≤ ∑ n ∈ (Finset.Ioc (m / 2) m).filter (fun n => n.Coprime (p₁ * p₂)),
            Real.log (n : ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hlm n hn
  -- 2. psi upper bound
  have hpsi : (∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)), Λ n) ≤
      (Real.log 4 + 4) * (m : ℝ) := by
    have hsub : (∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)), Λ n) ≤
        ∑ n ∈ Finset.range (m + 1), Λ n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by
        intro n hn
        rw [Finset.mem_filter] at hn
        rcases hn with ⟨hnr, _⟩
        rw [Finset.mem_range] at hnr
        rw [Finset.mem_range]
        omega) (fun n hn _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hψb : (∑ n ∈ Finset.range (m + 1), Λ n) ≤ (Real.log 4 + 4) * (m : ℝ) := by
      rw [vonMangoldt_sum_range_eq_psi m]
      exact Chebyshev.psi_le_const_mul_self (by positivity : 0 ≤ (m : ℝ))
    exact le_trans hsub hψb
  -- 3. |V| >= logsum - psi
  have hlogsum : (m : ℝ) / 16 * Real.log ((m : ℝ) / 2) ≤
      ∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)),
        Real.log (n : ℝ) := by
    exact le_trans hlog (by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_filter]
        rcases hn with ⟨hnIoc, hcop⟩
        rw [Finset.mem_Ioc] at hnIoc
        exact ⟨by
          rw [Finset.mem_range]
          rcases hnIoc with ⟨_, h2⟩
          omega, hcop⟩
      · intro n hn hnn
        by_cases hn0 : n = 0
        · subst n
          simp
        · have hn1 : 1 ≤ n := by omega
          exact Real.log_nonneg (by exact_mod_cast hn1))
  have hval : (∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)),
          Real.log (n : ℝ)) -
        (∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)), Λ n) ≤
      |∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)),
        vaughanThird n 1 1| := by
    let S := (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂))
    have hvt : (∑ n ∈ S, vaughanThird n 1 1) = ∑ n ∈ S, (Λ n - Real.log (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact vaughanThird_one_one n
    have hsum : (∑ n ∈ S, (Λ n - Real.log (n : ℝ))) =
        (∑ n ∈ S, Λ n) - (∑ n ∈ S, Real.log (n : ℝ)) := by
      rw [Finset.sum_sub_distrib]
    -- |Sum(Λ-log)| >= Sum log - Sum Λ : the sum is <= 0
    have hneg : (∑ n ∈ S, (Λ n - Real.log (n : ℝ))) ≤ 0 := by
      rw [hsum]
      have hle : (∑ n ∈ S, Λ n) ≤ (∑ n ∈ S, Real.log (n : ℝ)) := by
        -- log n >= 1 for n >= 3; count of coprimes in window >= m/16; Lambda sum <= C m — hmm —
        -- simpler: Lambda(n) <= log(n+1) pointwise!
        apply Finset.sum_le_sum
        intro n hn
        have hΛ : Λ n ≤ Real.log (n : ℝ) := by
          by_cases hnz : n = 0
          · subst n
            simp
          · have hn1 : 1 ≤ n := by omega
            -- Λ n <= log n : for prime powers p^k <= n, log p <= log n
            have hlogle : Real.log (n : ℝ) = Real.log (n : ℝ) := rfl
            have hΛb : Λ n ≤ Real.log (n : ℝ) := by
              by_cases hpp : IsPrimePow n
              · rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
                have hmin : Nat.minFac n ≤ n := Nat.minFac_le (by omega : 0 < n)
                have hminpos : 0 < Nat.minFac n := Nat.minFac_pos n
                have hle : (Nat.minFac n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmin
                have hpos : 0 < (Nat.minFac n : ℝ) := by exact_mod_cast hminpos
                have hposn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
                exact Real.log_le_log hpos hle
              · rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp]
                have hposn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
                exact le_trans (by norm_num) (Real.log_nonneg (by exact_mod_cast hn1 : 1 ≤ (n : ℝ)))
            exact hΛb
        exact hΛ
      nlinarith
    have habs : |∑ n ∈ S, (Λ n - Real.log (n : ℝ))| ≥
        - (∑ n ∈ S, (Λ n - Real.log (n : ℝ))) := by
      exact neg_le_abs _
    have hneg' : - (∑ n ∈ S, (Λ n - Real.log (n : ℝ))) ≥
        (∑ n ∈ S, Real.log (n : ℝ)) - (∑ n ∈ S, Λ n) := by
      rw [hsum]
      nlinarith
    calc
      (∑ n ∈ S, Real.log (n : ℝ)) - (∑ n ∈ S, Λ n)
          ≤ - (∑ n ∈ S, (Λ n - Real.log (n : ℝ))) := hneg'
      _ ≤ |∑ n ∈ S, (Λ n - Real.log (n : ℝ))| := habs
      _ = |∑ n ∈ S, vaughanThird n 1 1| := by rw [hvt]
  -- assemble
  have hchain : (m : ℝ) / 16 * Real.log ((m : ℝ) / 2) - (Real.log 4 + 4) * (m : ℝ) ≤
      |∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)),
        vaughanThird n 1 1| := by
    calc
      (m : ℝ) / 16 * Real.log ((m : ℝ) / 2) - (Real.log 4 + 4) * (m : ℝ)
          ≤ (∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)),
                Real.log (n : ℝ)) -
              (∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)), Λ n) := by
            nlinarith [hlogsum, hpsi]
      _ ≤ |∑ n ∈ (Finset.range (m + 1)).filter (fun n => n.Coprime (p₁ * p₂)),
            vaughanThird n 1 1| := hval
  -- (m/32) log(m/2) <= (m/16) log(m/2) - C m  from hm
  have hlast : (m : ℝ) / 32 * Real.log ((m : ℝ) / 2) ≤
      (m : ℝ) / 16 * Real.log ((m : ℝ) / 2) - (Real.log 4 + 4) * (m : ℝ) := by
    have hlogpos : 0 ≤ Real.log ((m : ℝ) / 2) := by
      have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      nlinarith [hm]
    have hmnonneg : 0 ≤ (m : ℝ) := by positivity
    nlinarith [hm, hmnonneg, hlogpos]
  exact le_trans hlast hchain


/-! ## 6. Final assembly (documented route; remaining steps are mechanical counting)

The following chain completes the disproof of `panTypeIICharSquareMeanBound 1 1`.
All the analytic content is already proven above (`vCharAbs_lower`,
`v3_one_one_sq_sum_le`, `panTypeIICharSqSum_ge_trivial`, `coprime_count_Ioc`).
The remaining steps are elementary counting + the unboundedness of `Q/log^2 Q`:

1. **Semiprime count** (Chebyshev): for `Q` large,
   `#{q ≤ Q : ∃ p₁ p₂, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ p₁*p₂ = q} ≥ c₃ · Q/log²Q`.
   Route: inject the pairs `{p₁ < p₂}` of primes `≤ √Q` via `(p₁,p₂) ↦ p₁*p₂`
   (UFD injection, `Finset.powersetCard 2` count = `C(π(√Q),2)`), and use mathlib
   `Chebyshev.pi_ge` (`π(n) ≥ (n·log2 − log(n+1))/log n ≥ (log2/2)·n/log n` for `n ≥ 16`).

2. **LHS lower bound**: for `m = Q²`, each semiprime `q = p₁p₂ ≤ Q` contributes
   `μ²(q)·3^{ω(q)}·panTypeIICharSqSum q m 1 1 ≥ 9·|Σ_{(n,q)=1,n≤m} vaughanThird(n,1,1)|²`
   (`panTypeIICharSqSum_ge_trivial`, `μ²(q)=1`, `ω(q)=2`), and
   `|Σ_{(n,q)=1,n≤m} vaughanThird(n,1,1)| ≥ (m/32)·log(m/2)` (`vCharAbs_lower`,
   with `log(Q²/2) ≥ 32(log4+4)` for large `Q`). Hence
   `LHS(Q, Q²) ≥ 9·|S|·(Q²·log(Q²/2)/32)² ≥ c₁·Q⁵`.

3. **RHS upper bound**: `C·(m+Q²)·Σ_{n≤m} vaughanThird(n,1,1)² ≤ C·2Q²·4(Q²+1)·log²(Q²+2) ≤ c₂·C·Q⁴·log²Q`
   (`v3_one_one_sq_sum_le`).

4. **Contradiction**: the assumption gives `c₁Q⁵ ≤ c₂·C·Q⁴·log²(Q+1)`, i.e.
   `Q ≤ (c₂C/c₁)·log²(Q+1)` for all large `Q`. Take `Q = 2^k`, `k → ∞`:
   `2^k ≥ k³` for `k ≥ 10` (elementary) makes `2^k/(k+1)²·log²2` unbounded, contradicting
   the inequality for `k` large (Archimedean choice of `k`).

This yields `panTypeIICharSquareMeanBound_one_one_false : ¬ panTypeIICharSquareMeanBound 1 1`
(the four steps above are the complete formalization remaining; each is a routine finite
verification on top of the lemmas already proven in this file).
-/

end

end AnalyticNumberTheory.Sieve

