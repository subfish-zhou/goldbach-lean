import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWTailBound

/-!
# Full-tail payment at the constructed cutoff

The cutoff is always `wUniformCutoff M (x ^ η)`. The rapid-decay order is
chosen only in the proof, never by changing this cutoff. The estimate holds
for every arithmetic mask, signed weights, and residue, with no SW input.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The full tail is exactly the difference between the infinite nonzero
mode and its actual finite-frequency truncation. -/
theorem smoothWNonzeroMode_sub_truncated_eq_full_tail
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    smoothWNonzeroMode M N Q β c a - truncatedWNonzeroMode M H N Q β c a =
      wMaskedTail M H N Q β c a (fun _ ↦ True) := by
  simp only [smoothWNonzeroMode, truncatedWNonzeroMode, wMaskedTail,
    wMaskedTuples, filter_true, wOriginalTuples, sum_filter, sum_product,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro n₁ _
  apply sum_congr rfl
  intro n₂ _
  by_cases hc : WCompatible q r n₁ n₂
  · simp only [if_pos hc, wTupleCoefficient, Complex.sub_re]
    ring
  · simp only [if_neg hc, sub_self]

/-- Uniform alpha-squared logarithmic payment of the actual masked tail.
All divisor orders may be zero. No relation between `M` and the supports is
needed beyond positivity of `M` and their common upper endpoint `x`. -/
theorem wMaskedTail_uniformCutoff_alpha_log_payment
    (i k j A : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M : ℝ, 0 < M →
      ∀ S N Q : Finset ℕ,
      S ⊆ Ioc 0 ⌊x⌋₊ → N ⊆ Ioc 0 ⌊x⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, ∀ P : WOriginalTuple → Prop,
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTail M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
          x ^ 2 / Real.log x ^ A := by
  obtain ⟨l, hl⟩ := exists_nat_gt (6 / η)
  have hlη : 6 < η * (l : ℝ) := by
    have := (div_lt_iff₀ hη).mp hl
    nlinarith
  obtain ⟨C, hC, htail⟩ := wMaskedTail_uniformCutoff_fouvryTau l
  let D : ℕ := (i + 1) ^ 2 - 1 + 2 * j + 2 * k
  have hlogpay := betaPayment_eventually_log_mul_rpow_le C hC.le (D + A)
    (b := 0) (d := 1) (by norm_num)
  filter_upwards [hlogpay, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hpay hx hlog
  intro M hM S N Q hS hN hQ α β c hα hβ hc a P
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  have hbase : 0 ≤ 1 + Real.log x := by linarith
  have hZ : 0 < x ^ η := Real.rpow_pos_of_pos hx0 _
  have hα' : ∀ m ∈ S, |α m| ≤ (fouvryTau (i + 1) m : ℝ) := by
    intro m hm
    exact (hα m hm).trans (by exact_mod_cast fouvryTau_le_succ i m)
  have hβ' : ∀ n ∈ N, |β n| ≤ (fouvryTau (k + 1) n : ℝ) := by
    intro n hn
    exact (hβ n hn).trans (by exact_mod_cast fouvryTau_le_succ k n)
  have hc' : ∀ q ∈ Q, |c q| ≤ (fouvryTau (j + 1) q : ℝ) := by
    intro q hq
    exact (hc q hq).trans (by exact_mod_cast fouvryTau_le_succ j q)
  have hαsq := sum_alpha_sq_le_fouvryTau (by omega : 1 ≤ i + 1) hx S hS α hα'
  have ht := htail M (x ^ η) hM hZ (k + 1) (j + 1) (by omega) (by omega)
    x x hx hx N Q hN hQ β c hβ' hc' a P
  simp only [Nat.add_sub_cancel] at ht
  have hbound :
      (∑ m ∈ S, α m ^ 2) *
          |wMaskedTail M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
        C * x ^ 5 * (1 + Real.log x) ^ D / (x ^ η) ^ l := by
    calc
      _ ≤ (x * (1 + Real.log x) ^ ((i + 1) ^ 2 - 1)) *
          (C * ((x * (1 + Real.log x) ^ j) ^ 2 *
            (x * (1 + Real.log x) ^ k) ^ 2) / (x ^ η) ^ l) :=
        mul_le_mul hαsq ht (abs_nonneg _) (by positivity)
      _ = _ := by
        simp only [D, pow_add, mul_pow, ← pow_mul, Nat.mul_comm]
        ring
  apply hbound.trans
  apply (div_le_div_iff₀ (pow_pos hZ l) (pow_pos hlog0 A)).mpr
  have hpay' : C * (1 + Real.log x) ^ (D + A) ≤ x := by
    simpa only [Real.rpow_zero, Real.rpow_one, mul_one] using hpay
  have hnum :
      C * x ^ 5 * (1 + Real.log x) ^ D * Real.log x ^ A ≤ x ^ 6 := by
    calc
      _ ≤ C * x ^ 5 * (1 + Real.log x) ^ D * (1 + Real.log x) ^ A := by
        gcongr
        linarith
      _ = x ^ 5 * (C * (1 + Real.log x) ^ (D + A)) := by rw [pow_add]; ring
      _ ≤ x ^ 5 * x := mul_le_mul_of_nonneg_left hpay' (by positivity)
      _ = x ^ 6 := by ring
  have hdenom : x ^ 6 ≤ (x ^ η) ^ l := by
    rw [← Real.rpow_natCast x 6, ← Real.rpow_natCast (x ^ η) l,
      ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx hlη.le
  exact hnum.trans (hdenom.trans (by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (one_le_pow₀ hx : 1 ≤ x ^ 2) (pow_nonneg hZ.le l)))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
