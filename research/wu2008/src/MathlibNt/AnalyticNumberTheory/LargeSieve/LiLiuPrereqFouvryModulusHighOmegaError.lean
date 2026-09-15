import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaConvolution

/-!
# High-omega signed modulus weights at the actual error

An arbitrary signed modulus weight supported on `omega(q) > ξ` gains
`2^(-ξ)` at the cost of doubling its fixed divisor order. For clean beta the
shift is nonzero, so the shifted divisor moment pays the progression sum
without any `x^epsilon` loss. No factorability of a masked weight is asserted.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def modulusHighOmegaLogExponent (i k j : ℕ) : ℕ :=
  (i + k) ^ 2 + (2 * j + 1) ^ 2 + i + k + 4 * j

theorem modulusHighOmega_abs_le_rankin (j : ℕ) (Q : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (ξ : ℝ)
    (hω : ∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ))
    {q : ℕ} (hq : q ∈ Q) :
    |c q| ≤ (2 : ℝ) ^ (-ξ) * fouvryTau (2 * j) q := by
  have he : betaHighOmega c ξ q = c q := by
    by_cases h : c q = 0
    · simp [betaHighOmega, h]
    · exact if_pos (hω q hq h)
  rw [← he]
  exact abs_betaHighOmega_le_rankin j hc ξ hq

theorem sum_modulusHighOmega_modEq_abs_le (j : ℕ) (Q : Finset ℕ)
    (c : ℕ → ℝ) (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (ξ : ℝ) (hω : ∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ))
    (m n : ℕ) (a : ℤ) (hne : (m : ℤ) * n - a ≠ 0) :
    (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤
      (2 : ℝ) ^ (-ξ) * fouvryTau (2 * j + 1) ((m : ℤ) * n - a).natAbs := by
  calc
    _ ≤ ∑ q ∈ Q, (2 : ℝ) ^ (-ξ) *
        (if Int.ModEq q ((m : ℤ) * n) a then |(fouvryTau (2 * j) q : ℝ)| else 0) := by
      apply sum_le_sum
      intro q hq
      split_ifs
      · simpa only [abs_of_nonneg (show (0 : ℝ) ≤ fouvryTau (2 * j) q from
          Nat.cast_nonneg _)] using
          modulusHighOmega_abs_le_rankin j Q c hc ξ hω hq
      · simp
    _ = (2 : ℝ) ^ (-ξ) * ∑ q ∈ Q,
        if Int.ModEq q ((m : ℤ) * n) a then |(fouvryTau (2 * j) q : ℝ)| else 0 :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_modEq_abs_le_fouvryTau (2 * j) Q
        (fun q => (fouvryTau (2 * j) q : ℝ)) (fun q _ => by simp) m n a hne)
      (Real.rpow_nonneg (by norm_num) _)

set_option maxHeartbeats 800000 in
/-- Uniform finite modulus deletion, for all fixed orders including zero and
all real cutoffs. Clean beta is used only to exclude `m*n=a`. -/
theorem modulusHighOmega_signedError_bound (i k j : ℕ)
    {U V x : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hUV : U * V ≤ x) (hUx : U ≤ x) (hVx : V ≤ x)
    (S N Q : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊U⌋₊)
    (hN : N ⊆ Ioc 0 ⌊V⌋₊) (hQ : Q ⊆ Ioc 0 ⌊x⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (a : ℤ) (ha : |(a : ℝ)| ≤ x)
    (hclean : ∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a)
    (ξ : ℝ) (hω : ∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ)) :
    |signedError S N Q α β c a| ≤
      6 * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j := by
  let H : ℝ := 1 + Real.log (2 * x)
  let C : ℝ := ∑ q ∈ Q, |c q| / (q.totient : ℝ)
  let P : ℕ → ℕ → ℝ := fun m n =>
    ∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0
  let D : ℕ := (i + k) ^ 2 + (2 * j + 1) ^ 2
  let E : ℕ := i + k + 4 * j
  have hgain : 0 ≤ (2 : ℝ) ^ (-ξ) := Real.rpow_nonneg (by norm_num) _
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
  have hCbound : C ≤ (2 : ℝ) ^ (-ξ) * H ^ (4 * j) := by
    calc
      _ ≤ ∑ q ∈ Q, ((2 : ℝ) ^ (-ξ) * fouvryTau (2 * j) q) / q.totient :=
        sum_le_sum (fun q hq => div_le_div_of_nonneg_right
          (modulusHighOmega_abs_le_rankin j Q c hc ξ hω hq) (Nat.cast_nonneg _))
      _ = (2 : ℝ) ^ (-ξ) * ∑ q ∈ Q,
          (fouvryTau (2 * j) q : ℝ) / q.totient := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        ring
      _ ≤ (2 : ℝ) ^ (-ξ) * ∑ q ∈ Ioc 0 ⌊x⌋₊,
          (fouvryTau (2 * j) q : ℝ) / q.totient :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)) hgain
      _ ≤ (2 : ℝ) ^ (-ξ) * (1 + Real.log x) ^ (4 * j) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [show 2 * (2 * j) = 4 * j by omega] using
            sum_fouvryTau_div_totient_le_real (2 * j) hx) hgain
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by have := Real.log_nonneg hx; linarith) (hlog hx le_rfl) _) hgain
  have hmassS : (∑ m ∈ S, (fouvryTau i m : ℝ)) ≤ U * H ^ i :=
    (highOmega_sum_tau_le i hU S hS).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by have := Real.log_nonneg hU; linarith) (hlog hU hUx) _)
        (by linarith))
  have hmassN : (∑ n ∈ N, (fouvryTau k n : ℝ)) ≤ V * H ^ k :=
    (highOmega_sum_tau_le k hV N hN).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by have := Real.log_nonneg hV; linarith) (hlog hV hVx) _)
        (by linarith))
  have hshift :
      (∑ n ∈ N, ∑ m ∈ S, (fouvryTau k n : ℝ) * fouvryTau i m *
        fouvryTau (2 * j + 1) ((m : ℤ) * n - a).natAbs) ≤ 5 * x * H ^ D := by
    calc
      _ = ∑ m ∈ S, ∑ n ∈ N, (fouvryTau i m : ℝ) * fouvryTau k n *
          fouvryTau (2 * j + 1) (((m * n : ℕ) : ℤ) - a).natAbs := by
        rw [sum_comm]
        apply sum_congr rfl
        intro m _
        apply sum_congr rfl
        intro n _
        push_cast
        ring
      _ ≤ ∑ t ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (i + k) t : ℝ) *
          fouvryTau (2 * j + 1) ((t : ℤ) - a).natAbs :=
        highOmega_convolution_le i k S N ⌊x⌋₊ hprod
          (fun t => (fouvryTau (2 * j + 1) ((t : ℤ) - a).natAbs : ℝ))
          (fun _ => Nat.cast_nonneg _)
      _ ≤ _ := highOmega_shifted_tau_sum_le (i + k) (2 * j + 1) hx a ha
  have hmain : (∑ n ∈ N, (fouvryTau k n : ℝ)) *
      (∑ m ∈ S, (fouvryTau i m : ℝ)) * H ^ (4 * j) ≤ x * H ^ E := by
    calc
      _ ≤ (V * H ^ k) * (U * H ^ i) * H ^ (4 * j) := by gcongr
      _ = (U * V) * H ^ E := by dsimp [E]; simp only [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hUV (pow_nonneg hH0 _)
  have hrow (n : ℕ) (hn : n ∈ N) (m : ℕ) (hm : m ∈ S) :
      |β n| * (|α m| * (P m n + C)) ≤
        (2 : ℝ) ^ (-ξ) * ((fouvryTau k n : ℝ) * fouvryTau i m *
          ((fouvryTau (2 * j + 1) ((m : ℤ) * n - a).natAbs : ℝ) + H ^ (4 * j))) := by
    by_cases hb : β n = 0
    · rw [hb, abs_zero, zero_mul]
      positivity
    have hpbound : P m n ≤
        (2 : ℝ) ^ (-ξ) * fouvryTau (2 * j + 1) ((m : ℤ) * n - a).natAbs :=
      sum_modulusHighOmega_modEq_abs_le j Q c hc ξ hω m n a
        (mul_sub_ne_zero_of_not_dvd m n a (hclean n hn hb))
    calc
      _ ≤ (fouvryTau k n : ℝ) * ((fouvryTau i m : ℝ) *
          ((2 : ℝ) ^ (-ξ) * fouvryTau (2 * j + 1) ((m : ℤ) * n - a).natAbs +
            (2 : ℝ) ^ (-ξ) * H ^ (4 * j))) := by
        apply mul_le_mul (hβ n hn)
        · exact mul_le_mul (hα m hm) (add_le_add hpbound hCbound)
            (add_nonneg (hP m n) hC) (Nat.cast_nonneg _)
        · exact mul_nonneg (abs_nonneg _) (add_nonneg (hP m n) hC)
        · positivity
      _ = _ := by ring
  have hD : H ^ D ≤ H ^ modulusHighOmegaLogExponent i k j :=
    pow_le_pow_right₀ hH (by dsimp [D, modulusHighOmegaLogExponent]; omega)
  have hE : H ^ E ≤ H ^ modulusHighOmegaLogExponent i k j :=
    pow_le_pow_right₀ hH (by dsimp [E, modulusHighOmegaLogExponent]; omega)
  calc
    _ ≤ ∑ n ∈ N, |β n| * ∑ m ∈ S, |α m| * (P m n + C) :=
      signedError_abs_le_product_majorant S N Q α β c a
    _ ≤ ∑ n ∈ N, ∑ m ∈ S, (2 : ℝ) ^ (-ξ) *
        ((fouvryTau k n : ℝ) * fouvryTau i m *
          ((fouvryTau (2 * j + 1) ((m : ℤ) * n - a).natAbs : ℝ) + H ^ (4 * j))) := by
      apply sum_le_sum
      intro n hn
      rw [mul_sum]
      exact sum_le_sum (fun m hm => hrow n hn m hm)
    _ = (2 : ℝ) ^ (-ξ) *
        ((∑ n ∈ N, ∑ m ∈ S, (fouvryTau k n : ℝ) * fouvryTau i m *
          fouvryTau (2 * j + 1) ((m : ℤ) * n - a).natAbs) +
          (∑ n ∈ N, (fouvryTau k n : ℝ)) *
            (∑ m ∈ S, (fouvryTau i m : ℝ)) * H ^ (4 * j)) := by
      simp only [mul_add, sum_add_distrib, mul_sum, sum_mul, mul_assoc]
      congr 1
      exact sum_comm
    _ ≤ (2 : ℝ) ^ (-ξ) * (5 * x * H ^ D + x * H ^ E) :=
      mul_le_mul_of_nonneg_left (add_le_add hshift hmain) hgain
    _ ≤ (2 : ℝ) ^ (-ξ) *
        (5 * x * H ^ modulusHighOmegaLogExponent i k j +
          x * H ^ modulusHighOmegaLogExponent i k j) := by gcongr
    _ = _ := by dsimp [H]; ring

theorem betaClean_modulusHighOmega_signedError_bound (i k j : ℕ)
    {U V x : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hUV : U * V ≤ x) (hUx : U ≤ x) (hVx : V ≤ x)
    (S N Q : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊U⌋₊)
    (hN : N ⊆ Ioc 0 ⌊V⌋₊) (hQ : Q ⊆ Ioc 0 ⌊x⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (a : ℤ) (ha : |(a : ℝ)| ≤ x)
    (ξ : ℝ) (hω : ∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ)) :
    |signedError S N Q α (betaClean β a) c a| ≤
      6 * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j :=
  modulusHighOmega_signedError_bound i k j hU hV hx hUV hUx hVx S N Q hS hN hQ
    α (betaClean β a) c hα (betaClean_abs_le_fouvryTau hβ a) hc a ha
    (fun _ _ hn => betaClean_nonzero_not_dvd hn) ξ hω

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
