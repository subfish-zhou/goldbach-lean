import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmega

/-!
# Shifted divisor moments without a power loss

Regrouping the product `m*n` uses the exact divisor antidiagonal.
The absolute-value shift has at most two preimages. The inequality
`u*v ≤ u²+v²` then gives a uniform fixed logarithmic cost.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem highOmega_convolution_le (i k : ℕ) (S N : Finset ℕ) (X : ℕ)
    (hprod : ∀ m ∈ S, ∀ n ∈ N, 0 < m * n ∧ m * n ≤ X)
    (F : ℕ → ℝ) (hF : ∀ t, 0 ≤ F t) :
    (∑ m ∈ S, ∑ n ∈ N, (fouvryTau i m : ℝ) * fouvryTau k n * F (m * n)) ≤
      ∑ t ∈ Ioc 0 X, (fouvryTau (i + k) t : ℝ) * F t := by
  have hmap : ∀ p ∈ S ×ˢ N, p.1 * p.2 ∈ Ioc 0 X := by
    intro p hp
    obtain ⟨hm, hn⟩ := mem_product.mp hp
    exact mem_Ioc.mpr (hprod p.1 hm p.2 hn)
  have he : (∑ m ∈ S, ∑ n ∈ N,
      (fouvryTau i m : ℝ) * fouvryTau k n * F (m * n)) =
      ∑ p ∈ S ×ˢ N, (fouvryTau i p.1 : ℝ) * fouvryTau k p.2 * F (p.1 * p.2) := by
    rw [sum_product]
  rw [he, ← sum_fiberwise_of_maps_to hmap]
  apply sum_le_sum
  intro t ht
  have hsub : (S ×ˢ N).filter (fun p : ℕ × ℕ => p.1 * p.2 = t) ⊆
      t.divisorsAntidiagonal := by
    intro p hp
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨(mem_filter.mp hp).2, (mem_Ioc.mp ht).1.ne'⟩
  calc
    _ = ∑ p ∈ (S ×ˢ N).filter (fun p : ℕ × ℕ => p.1 * p.2 = t),
        (fouvryTau i p.1 : ℝ) * fouvryTau k p.2 * F t :=
      sum_congr rfl (fun p hp => by rw [(mem_filter.mp hp).2])
    _ ≤ ∑ p ∈ t.divisorsAntidiagonal,
        (fouvryTau i p.1 : ℝ) * fouvryTau k p.2 * F t :=
      sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => mul_nonneg (by positivity) (hF t))
    _ = _ := by
      rw [← sum_mul]
      congr 1
      simp only [fouvryTau, pow_add, ArithmeticFunction.mul_apply, Nat.cast_sum, Nat.cast_mul]

theorem highOmega_shift_fiber_card_le (S : Finset ℕ) (a : ℤ) (d : ℕ) :
    (S.filter (fun t : ℕ => ((t : ℤ) - a).natAbs = d)).card ≤ 2 := by
  have hsub : S.filter (fun t : ℕ => ((t : ℤ) - a).natAbs = d) ⊆
      {(a + (d : ℤ)).toNat, (a - (d : ℤ)).toNat} := by
    intro t ht
    have he : |(t : ℤ) - a| = (d : ℤ) := by
      rw [← Int.natCast_natAbs, (mem_filter.mp ht).2]
    rcases le_total 0 ((t : ℤ) - a) with h | h
    · rw [abs_of_nonneg h] at he
      have ht' : t = (a + (d : ℤ)).toNat := by omega
      simp [ht']
    · rw [abs_of_nonpos h] at he
      have ht' : t = (a - (d : ℤ)).toNat := by omega
      simp [ht']
  exact (card_le_card hsub).trans ((card_insert_le ..).trans (by simp))

theorem highOmega_shift_sum_le (S : Finset ℕ) (a : ℤ) (Y : ℕ)
    (hY : ∀ t ∈ S, ((t : ℤ) - a).natAbs ≤ Y)
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) (hF0 : F 0 = 0) :
    (∑ t ∈ S, F ((t : ℤ) - a).natAbs) ≤ 2 * ∑ d ∈ Ioc 0 Y, F d := by
  have hmap : ∀ t ∈ S, ((t : ℤ) - a).natAbs ∈ Icc 0 Y :=
    fun t ht => mem_Icc.mpr ⟨Nat.zero_le _, hY t ht⟩
  rw [← sum_fiberwise_of_maps_to' hmap]
  calc
    _ ≤ ∑ d ∈ Icc 0 Y, 2 * F d := by
      apply sum_le_sum
      intro d _
      simp only [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast highOmega_shift_fiber_card_le S a d) (hF d)
    _ = 2 * ∑ d ∈ Ioc 0 Y, F d := by
      rw [← mul_sum]
      congr 1
      symm
      apply sum_subset
      · intro d hd
        exact mem_Icc.mpr ⟨Nat.zero_le _, (mem_Ioc.mp hd).2⟩
      · intro d hd hn
        have hd0 : d = 0 := by
          simp only [mem_Icc, mem_Ioc] at hd hn
          omega
        simpa only [hd0] using hF0

theorem highOmega_shifted_tau_sum_le (r s : ℕ) {x : ℝ} (hx : 1 ≤ x)
    (a : ℤ) (ha : |(a : ℝ)| ≤ x) :
    (∑ t ∈ Ioc 0 ⌊x⌋₊,
      (fouvryTau r t : ℝ) * fouvryTau s ((t : ℤ) - a).natAbs) ≤
      5 * x * (1 + Real.log (2 * x)) ^ (r ^ 2 + s ^ 2) := by
  let H : ℝ := 1 + Real.log (2 * x)
  have hH : 1 ≤ H := by
    have := Real.log_nonneg (show 1 ≤ 2 * x by linarith)
    dsimp [H]
    linarith
  have hlog : 1 + Real.log x ≤ H := by
    have := Real.log_le_log (show 0 < x by linarith) (show x ≤ 2 * x by linarith)
    dsimp [H]
    linarith
  have hm (k : ℕ) : (∑ t ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k t : ℝ) ^ 2) ≤
      x * H ^ (k ^ 2) := by
    calc
      _ ≤ ∑ t ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k ^ 2) t : ℝ) :=
        sum_le_sum (fun t _ => by exact_mod_cast fouvryTau_sq_le k t)
      _ ≤ x * (1 + Real.log x) ^ (k ^ 2) :=
        highOmega_sum_tau_le _ hx _ (by rfl)
      _ ≤ _ := by
        gcongr
        have := Real.log_nonneg hx
        linarith
  have hs : (∑ t ∈ Ioc 0 ⌊x⌋₊, (fouvryTau s ((t : ℤ) - a).natAbs : ℝ) ^ 2) ≤
      4 * x * H ^ (s ^ 2) := by
    have hY : ∀ t ∈ Ioc 0 ⌊x⌋₊, ((t : ℤ) - a).natAbs ≤ ⌊2 * x⌋₊ := by
      intro t ht
      apply Nat.le_floor
      have ht' : (t : ℝ) ≤ x :=
        (by exact_mod_cast (mem_Ioc.mp ht).2 : (t : ℝ) ≤ ⌊x⌋₊).trans
          (Nat.floor_le (by linarith))
      calc
        _ = |(t : ℝ) - (a : ℝ)| := by simp
        _ ≤ |(t : ℝ)| + |(a : ℝ)| := abs_sub _ _
        _ ≤ 2 * x := by rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith
    calc
      _ ≤ 2 * ∑ d ∈ Ioc 0 ⌊2 * x⌋₊, (fouvryTau s d : ℝ) ^ 2 :=
        highOmega_shift_sum_le _ a _ hY _ (fun _ => sq_nonneg _) (by simp)
      _ ≤ 2 * ∑ d ∈ Ioc 0 ⌊2 * x⌋₊, (fouvryTau (s ^ 2) d : ℝ) := by
        gcongr with d _
        exact_mod_cast fouvryTau_sq_le s d
      _ ≤ 2 * ((2 * x) * H ^ (s ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (highOmega_sum_tau_le _ (by linarith : 1 ≤ 2 * x) _ (by rfl)) (by norm_num)
      _ = _ := by ring
  have hrpow : H ^ (r ^ 2) ≤ H ^ (r ^ 2 + s ^ 2) :=
    pow_le_pow_right₀ hH (by omega)
  have hspow : H ^ (s ^ 2) ≤ H ^ (r ^ 2 + s ^ 2) :=
    pow_le_pow_right₀ hH (by omega)
  calc
    _ ≤ ∑ t ∈ Ioc 0 ⌊x⌋₊,
        ((fouvryTau r t : ℝ) ^ 2 + (fouvryTau s ((t : ℤ) - a).natAbs : ℝ) ^ 2) := by
      apply sum_le_sum
      intro t _
      nlinarith [sq_nonneg ((fouvryTau r t : ℝ) -
        fouvryTau s ((t : ℤ) - a).natAbs)]
    _ ≤ x * H ^ (r ^ 2) + 4 * x * H ^ (s ^ 2) := by
      rw [sum_add_distrib]
      exact add_le_add (hm r) hs
    _ ≤ x * H ^ (r ^ 2 + s ^ 2) + 4 * x * H ^ (r ^ 2 + s ^ 2) := by gcongr
    _ = _ := by dsimp [H]; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
