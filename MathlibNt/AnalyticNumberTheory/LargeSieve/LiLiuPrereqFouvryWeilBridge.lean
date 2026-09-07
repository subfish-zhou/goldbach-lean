import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompletion
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.ZMod.Coprime

/-!
# The exact interval and gcd form of the conditional Weil-to-Fouvry bridge

The complete Kloosterman estimate is an explicit hypothesis, not a proved
input. The interval conversion and the divisor/logarithm payment are proved.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {q : ℕ} [NeZero q]

def reciprocalInterval (q : ℕ) [NeZero q] (d : ℤ) (X Y : ℝ) : ℂ :=
  ∑ c ∈ Ioc ⌊X⌋ ⌊Y⌋, reciprocalPhase q d (c : ZMod q)

theorem reciprocalInterval_eq_coprime_sum (d : ℤ) (X Y : ℝ) :
    reciprocalInterval q d X Y =
      ∑ c ∈ (Ioc ⌊X⌋ ⌊Y⌋).filter (fun c : ℤ ↦ IsCoprime (q : ℤ) c),
        ZMod.stdAddChar ((d : ZMod q) * (c : ZMod q)⁻¹) := by
  classical
  simp only [reciprocalInterval, reciprocalPhase, sum_filter,
    ZMod.coe_int_isUnit_iff_isCoprime]

theorem mem_reciprocalInterval (c : ℤ) (X Y : ℝ) :
    c ∈ Ioc ⌊X⌋ ⌊Y⌋ ↔ X < (c : ℝ) ∧ (c : ℝ) ≤ Y := by
  simp only [mem_Ioc, Int.floor_lt, Int.le_floor]

theorem reciprocalInterval_eq_incomplete (d : ℤ) {X Y : ℝ} (hXY : X ≤ Y) :
    reciprocalInterval q d X Y =
      incompleteReciprocal q d (⌊X⌋ + 1) (⌊Y⌋ - ⌊X⌋).toNat := by
  have hfloor : ⌊X⌋ ≤ ⌊Y⌋ := Int.floor_mono hXY
  unfold reciprocalInterval incompleteReciprocal
  symm
  refine sum_bij (fun j _ ↦ ⌊X⌋ + 1 + (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_range] at hj
    simp only [mem_Ioc]
    omega
  · intro a _ b _ hab
    omega
  · intro c hc
    simp only [mem_Ioc] at hc
    refine ⟨(c - (⌊X⌋ + 1)).toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro j _
    congr 1
    push_cast
    rfl

omit [NeZero q] in
theorem reciprocalInterval_length_le {X Y : ℝ} (h : Y - X ≤ q) :
    (⌊Y⌋ - ⌊X⌋).toNat ≤ q := by
  have hf := Int.floor_mono (show Y ≤ X + (q : ℝ) by linarith)
  rw [Int.floor_add_natCast] at hf
  omega

/-- A pointwise fixed-order moment bound extracted from the proved full mean. -/
theorem fouvryTau_pow_pointwise (k r : ℕ) (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) :
    (fouvryTau k n : ℝ) ^ r ≤
      (n : ℝ) * (1 + Real.log n) ^ (k ^ r - 1) := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 n, (fouvryTau k m : ℝ) ^ r :=
      single_le_sum (fun _ _ ↦ by positivity) (mem_Ioc.mpr ⟨hn, le_rfl⟩)
    _ ≤ _ := by
      simpa only [Nat.floor_natCast] using
        sum_fouvryTau_pow_le_real (r := r) hk (show (1 : ℝ) ≤ n by exact_mod_cast hn)

/-- Arbitrarily high fixed moments pay the exact divisor/logarithm completion
loss. The threshold is uniform in the positive integer argument. -/
theorem eventually_divisors_completion_loss {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.divisors.card : ℝ) * (3 + 2 * Real.log n) ≤ (n : ℝ) ^ ε := by
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / ε)
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    simp only [Nat.cast_zero] at hr
    have := one_div_pos.mpr hε
    linarith
  have hgap : 0 < ε * r - 1 := by
    have := (div_lt_iff₀ hε).mp hr
    nlinarith
  let K := 2 ^ r - 1
  have hs : (fun x : ℝ ↦ Real.log x ^ (K + r)) =o[atTop]
      (fun x ↦ x ^ (ε * r - 1)) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (K + r : ℕ) hgap
  have hb := (hs.const_mul_left ((2 : ℝ) ^ K * 5 ^ r)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hevent : ∀ᶠ x : ℝ in atTop,
      1 ≤ Real.log x ∧ 1 ≤ x ∧
      2 ^ K * 5 ^ r * Real.log x ^ (K + r) ≤ x ^ (ε * r - 1) := by
    filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℝ)] with x hx hl hx1
    refine ⟨hl, hx1, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (2 : ℝ) ^ K * 5 ^ r * Real.log x ^ (K + r)),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _), one_mul] using hx
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hevent,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rcases hn with ⟨hlog, hnR, hpay⟩
  have hn0 : (0 : ℝ) < n := by positivity
  have hm := fouvryTau_pow_pointwise 2 r (by norm_num) (by omega : 0 < n)
  rw [fouvryTau_two] at hm
  apply le_of_pow_le_pow_left₀ hr0 (Real.rpow_nonneg hn0.le ε)
  calc
    ((n.divisors.card : ℝ) * (3 + 2 * Real.log n)) ^ r
      ≤ ((n : ℝ) * (1 + Real.log n) ^ K) * (3 + 2 * Real.log n) ^ r := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hm (by positivity)
    _ ≤ ((n : ℝ) * (2 * Real.log n) ^ K) * (5 * Real.log n) ^ r := by
      gcongr <;> linarith
    _ = (n : ℝ) * (2 ^ K * 5 ^ r * Real.log n ^ (K + r)) := by
      rw [pow_add, mul_pow, mul_pow]
      ring
    _ ≤ (n : ℝ) * (n : ℝ) ^ (ε * r - 1) :=
      mul_le_mul_of_nonneg_left hpay hn0.le
    _ = ((n : ℝ) ^ ε) ^ r := by
      rw [← Real.rpow_mul_natCast hn0.le, mul_comm (n : ℝ),
        ← Real.rpow_add_one hn0.ne', sub_add_cancel]

/-- A single constant covers all moduli, not merely sufficiently large ones. -/
theorem divisors_completion_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) * (3 + 2 * Real.log n) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (eventually_divisors_completion_loss hε))
  let C : ℝ := 1 + (N : ℝ) * (3 + 2 * N)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (le_of_lt (lt_of_not_ge hlarge))
    have hdiv : (n.divisors.card : ℝ) ≤ N :=
      (by exact_mod_cast Nat.card_divisors_le_self n : (n.divisors.card : ℝ) ≤ n).trans hnN
    have hlog : Real.log n ≤ N := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
      linarith
    calc
      _ ≤ (N : ℝ) * (3 + 2 * N) := by
        gcongr
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp

theorem completeKloosterman_gcd_envelope (d : ℤ)
    (hWeil : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) *
        Real.sqrt (q.gcd (m.val.gcd d.natAbs)) * Real.sqrt q) :
    ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd d.natAbs) * Real.sqrt q := by
  intro m
  apply (hWeil m).trans
  gcongr
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (NeZero.pos q))
    (Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)))

/-- Exact F87 Lemma 3 interval and frequency domain, conditional ONLY on the
complete Weil input, which remains an unproved external formalization frontier. -/
theorem reciprocalInterval_weil_to_fouvry
    (hWeil : ∀ (q : ℕ) (_ : NeZero q) (m : ZMod q) (d : ℤ),
      ‖completeKloosterman q m d‖ ≤ (q.divisors.card : ℝ) *
        Real.sqrt (q.gcd (m.val.gcd d.natAbs)) * Real.sqrt q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (X Y : ℝ),
      X ≤ Y → Y - X ≤ q →
      ‖reciprocalInterval q d X Y‖ ≤
        C * Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hpay⟩ := divisors_completion_loss hε
  refine ⟨C, hC, ?_⟩
  intro q hq d X Y hXY hlen
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  rw [reciprocalInterval_eq_incomplete d hXY]
  calc
    _ ≤ (3 + 2 * Real.log q) *
        ((q.divisors.card : ℝ) * Real.sqrt (q.gcd d.natAbs) * Real.sqrt q) :=
      incompleteReciprocal_norm_le_log d (⌊X⌋ + 1) _ (reciprocalInterval_length_le hlen) _
        (completeKloosterman_gcd_envelope d (hWeil q hq · d))
    _ = ((q.divisors.card : ℝ) * (3 + 2 * Real.log q)) *
        Real.sqrt (q.gcd d.natAbs) * Real.sqrt q := by ring
    _ ≤ (C * (q : ℝ) ^ ε) * Real.sqrt (q.gcd d.natAbs) * Real.sqrt q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpay q (NeZero.pos q)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by
      simp only [Real.sqrt_eq_rpow]
      rw [Real.rpow_add hqR]
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
