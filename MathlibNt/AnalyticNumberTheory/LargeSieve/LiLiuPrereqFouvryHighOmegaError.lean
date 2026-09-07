import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaConvolution

/-!
# High-omega deletion at the original signed error

No well-factorability claim is made for a masked modulus sequence: the
original signed `c` is retained throughout. Clean beta excludes the equality
progression before the modulus divisor bound is used.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def highOmegaLogExponent (i k j : ℕ) : ℕ :=
  (i + 2 * k) ^ 2 + (j + 1) ^ 2 + i + 2 * k + 2 * j

set_option maxHeartbeats 800000 in
/-- Finite, explicit high-omega deletion. The three orders can be zero.
Only elementary global divisor means occur, so the saving is exponential
in the actual real cutoff, not weakened by an `x^epsilon` factor. -/
theorem highOmega_signedError_bound (i k j : ℕ)
    {U V x : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hUV : U * V ≤ x) (hUx : U ≤ x) (hVx : V ≤ x)
    (S N Q : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊U⌋₊)
    (hN : N ⊆ Ioc 0 ⌊V⌋₊) (hQ : Q ⊆ Ioc 0 ⌊x⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (a : ℤ) (ha : |(a : ℝ)| ≤ x)
    (hclean : ∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) (ξ : ℝ) :
    |signedError S N Q α (betaHighOmega β ξ) c a| ≤
      6 * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ highOmegaLogExponent i k j := by
  let H : ℝ := 1 + Real.log (2 * x)
  let C : ℝ := ∑ q ∈ Q, |c q| / (q.totient : ℝ)
  let P : ℕ → ℕ → ℝ := fun m n =>
    ∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0
  let D : ℕ := (i + 2 * k) ^ 2 + (j + 1) ^ 2
  let E : ℕ := i + 2 * k + 2 * j
  have hH : 1 ≤ H := by
    have := Real.log_nonneg (show 1 ≤ 2 * x by linarith)
    dsimp [H]
    linarith
  have hH0 : 0 ≤ H := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hP (m n : ℕ) : 0 ≤ P m n := by
    apply sum_nonneg
    intro q _
    split_ifs <;> positivity
  have hlog {y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) : 1 + Real.log y ≤ H := by
    have := Real.log_le_log (show 0 < y by linarith) (show y ≤ 2 * x by linarith)
    dsimp [H]
    linarith
  have hprod : ∀ m ∈ S, ∀ n ∈ N, 0 < m * n ∧ m * n ≤ ⌊x⌋₊ := by
    intro m hm n hn
    obtain ⟨hm0, hmU⟩ := mem_Ioc.mp (hS hm)
    obtain ⟨hn0, hnV⟩ := mem_Ioc.mp (hN hn)
    refine ⟨Nat.mul_pos hm0 hn0, Nat.le_floor ?_⟩
    have hm' : (m : ℝ) ≤ U :=
      (by exact_mod_cast hmU : (m : ℝ) ≤ ⌊U⌋₊).trans (Nat.floor_le (by linarith))
    have hn' : (n : ℝ) ≤ V :=
      (by exact_mod_cast hnV : (n : ℝ) ≤ ⌊V⌋₊).trans (Nat.floor_le (by linarith))
    push_cast
    exact (mul_le_mul hm' hn' (Nat.cast_nonneg _) (by linarith)).trans hUV
  have hCbound : C ≤ H ^ (2 * j) := by
    calc
      _ ≤ ∑ q ∈ Q, (fouvryTau j q : ℝ) / q.totient :=
        sum_le_sum (fun q hq => div_le_div_of_nonneg_right (hc q hq) (Nat.cast_nonneg _))
      _ ≤ ∑ q ∈ Ioc 0 ⌊x⌋₊, (fouvryTau j q : ℝ) / q.totient :=
        sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)
      _ ≤ (1 + Real.log x) ^ (2 * j) := sum_fouvryTau_div_totient_le_real j hx
      _ ≤ _ := pow_le_pow_left₀ (by have := Real.log_nonneg hx; linarith) (hlog hx le_rfl) _
  have hmassS : (∑ m ∈ S, (fouvryTau i m : ℝ)) ≤ U * H ^ i :=
    (highOmega_sum_tau_le i hU S hS).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by have := Real.log_nonneg hU; linarith) (hlog hU hUx) _)
        (by linarith))
  have hmassN : (∑ n ∈ N, (fouvryTau (2 * k) n : ℝ)) ≤ V * H ^ (2 * k) :=
    (highOmega_sum_tau_le (2 * k) hV N hN).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by have := Real.log_nonneg hV; linarith) (hlog hV hVx) _)
        (by linarith))
  have hshift :
      (∑ n ∈ N, ∑ m ∈ S, (fouvryTau (2 * k) n : ℝ) * fouvryTau i m *
        fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs) ≤ 5 * x * H ^ D := by
    calc
      _ = ∑ m ∈ S, ∑ n ∈ N, (fouvryTau i m : ℝ) * fouvryTau (2 * k) n *
          fouvryTau (j + 1) (((m * n : ℕ) : ℤ) - a).natAbs := by
        rw [sum_comm]
        apply sum_congr rfl
        intro m _
        apply sum_congr rfl
        intro n _
        push_cast
        ring
      _ ≤ ∑ t ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (i + 2 * k) t : ℝ) *
          fouvryTau (j + 1) ((t : ℤ) - a).natAbs :=
        highOmega_convolution_le i (2 * k) S N ⌊x⌋₊ hprod
          (fun t => (fouvryTau (j + 1) ((t : ℤ) - a).natAbs : ℝ))
          (fun _ => Nat.cast_nonneg _)
      _ ≤ _ := highOmega_shifted_tau_sum_le (i + 2 * k) (j + 1) hx a ha
  have hmain : (∑ n ∈ N, (fouvryTau (2 * k) n : ℝ)) *
      (∑ m ∈ S, (fouvryTau i m : ℝ)) * C ≤ x * H ^ E := by
    calc
      _ ≤ (V * H ^ (2 * k)) * (U * H ^ i) * H ^ (2 * j) := by gcongr
      _ = (U * V) * H ^ E := by dsimp [E]; simp only [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hUV (pow_nonneg hH0 _)
  have hrow (n : ℕ) (hn : n ∈ N) (m : ℕ) (hm : m ∈ S) :
      |betaHighOmega β ξ n| * (|α m| * (P m n + C)) ≤
        (2 : ℝ) ^ (-ξ) * ((fouvryTau (2 * k) n : ℝ) * fouvryTau i m *
          ((fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) + C)) := by
    by_cases hb : betaHighOmega β ξ n = 0
    · rw [hb, abs_zero, zero_mul]
      positivity
    have hb' : β n ≠ 0 := by
      intro he
      apply hb
      simp [betaHighOmega, he]
    have hpbound : P m n ≤ (fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) :=
      sum_modEq_abs_le_fouvryTau j Q c hc m n a
        (mul_sub_ne_zero_of_not_dvd m n a (hclean n hn hb'))
    calc
      _ ≤ ((2 : ℝ) ^ (-ξ) * fouvryTau (2 * k) n) *
          ((fouvryTau i m : ℝ) *
            ((fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) + C)) := by
        apply mul_le_mul (abs_betaHighOmega_le_rankin k hβ ξ hn)
        · exact mul_le_mul (hα m hm) (add_le_add hpbound le_rfl)
            (add_nonneg (hP m n) hC) (Nat.cast_nonneg _)
        · exact mul_nonneg (abs_nonneg _) (add_nonneg (hP m n) hC)
        · positivity
      _ = _ := by ring
  have hgain : 0 ≤ (2 : ℝ) ^ (-ξ) := Real.rpow_nonneg (by norm_num) _
  have hD : H ^ D ≤ H ^ highOmegaLogExponent i k j :=
    pow_le_pow_right₀ hH (by dsimp [D, highOmegaLogExponent]; omega)
  have hE : H ^ E ≤ H ^ highOmegaLogExponent i k j :=
    pow_le_pow_right₀ hH (by dsimp [E, highOmegaLogExponent]; omega)
  calc
    _ ≤ ∑ n ∈ N, |betaHighOmega β ξ n| * ∑ m ∈ S, |α m| * (P m n + C) :=
      signedError_abs_le_product_majorant S N Q α (betaHighOmega β ξ) c a
    _ ≤ ∑ n ∈ N, ∑ m ∈ S, (2 : ℝ) ^ (-ξ) *
        ((fouvryTau (2 * k) n : ℝ) * fouvryTau i m *
          ((fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) + C)) := by
      apply sum_le_sum
      intro n hn
      rw [mul_sum]
      exact sum_le_sum (fun m hm => hrow n hn m hm)
    _ = (2 : ℝ) ^ (-ξ) *
        ((∑ n ∈ N, ∑ m ∈ S, (fouvryTau (2 * k) n : ℝ) * fouvryTau i m *
          fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs) +
          (∑ n ∈ N, (fouvryTau (2 * k) n : ℝ)) *
            (∑ m ∈ S, (fouvryTau i m : ℝ)) * C) := by
      simp only [mul_add, sum_add_distrib, mul_sum, sum_mul, mul_assoc]
      congr 1
      exact sum_comm
    _ ≤ (2 : ℝ) ^ (-ξ) * (5 * x * H ^ D + x * H ^ E) :=
      mul_le_mul_of_nonneg_left (add_le_add hshift hmain) hgain
    _ ≤ (2 : ℝ) ^ (-ξ) *
        (5 * x * H ^ highOmegaLogExponent i k j + x * H ^ highOmegaLogExponent i k j) := by
      gcongr
    _ = _ := by dsimp [H]; ring

theorem betaClean_highOmega_signedError_bound (i k j : ℕ)
    {U V x : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hUV : U * V ≤ x) (hUx : U ≤ x) (hVx : V ≤ x)
    (S N Q : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊U⌋₊)
    (hN : N ⊆ Ioc 0 ⌊V⌋₊) (hQ : Q ⊆ Ioc 0 ⌊x⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (a : ℤ) (ha : |(a : ℝ)| ≤ x) (ξ : ℝ) :
    |signedError S N Q α (betaHighOmega (betaClean β a) ξ) c a| ≤
      6 * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ highOmegaLogExponent i k j :=
  highOmega_signedError_bound i k j hU hV hx hUV hUx hVx S N Q hS hN hQ
    α (betaClean β a) c hα (betaClean_abs_le_fouvryTau hβ a) hc a ha
    (fun _ _ hn => betaClean_nonzero_not_dvd hn) ξ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
