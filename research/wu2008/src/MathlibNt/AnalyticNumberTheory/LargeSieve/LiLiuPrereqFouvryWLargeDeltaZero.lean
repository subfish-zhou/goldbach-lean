import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDZero

/-!
# The same-mask zero mode for a large common modulus

Every further submask of `gcd(q,r)>Y` is allowed, without symmetry or
positivity assumptions on the mask or coefficients. Absolute values are
enlarged to the full symmetric congruence relation before applying the
quadratic energy bound. The exact lcm denominator is retained throughout.

This bounds the actual masked zero mode, not a centered covariance or
Siegel--Walfisz cancellation restricted to a mask. The original progression
sum, nonzero modes, and their signed-error composition are separate results.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Quotients distinguish the elements of a fixed residue class. -/
theorem card_modEq_row_le (K d n : ℕ) (N : Finset ℕ) (hN : N ⊆ Ioc 0 K) :
    (N.filter (fun m ↦ Nat.ModEq d n m)).card ≤ K / d + 1 := by
  calc
    _ ≤ (range (K / d + 1)).card := by
      apply card_le_card_of_injOn (fun m : ℕ ↦ m / d)
      · intro m hm
        exact mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (mem_Ioc.mp (hN (mem_filter.mp hm).1)).2))
      · intro m hm b hb he
        exact Nat.ext_div_modEq he
          ((mem_filter.mp hm).2.symm.trans (mem_filter.mp hb).2)
    _ = _ := card_range _

/-- The full congruence relation is symmetric; its row bound pays the
absolute beta products by the quadratic beta mass. -/
theorem sum_abs_modEq_pairs_le {T Y : ℝ} (hT : 1 ≤ T) (hY : 0 < Y)
    (d : ℕ) (hd : Y < (d : ℝ)) (N : Finset ℕ)
    (hN : N ⊆ Ioc 0 ⌊T⌋₊) (β : ℕ → ℝ) :
    (∑ p ∈ N ×ˢ N, if Nat.ModEq d p.1 p.2 then |β p.1 * β p.2| else 0) ≤
      (T / Y + 1) * ∑ n ∈ N, β n ^ 2 := by
  let E := ∑ n ∈ N, β n ^ 2 *
    ((N.filter (fun m ↦ Nat.ModEq d n m)).card : ℝ)
  have hrow (n : ℕ) :
      ((N.filter (fun m ↦ Nat.ModEq d n m)).card : ℝ) ≤ T / Y + 1 := by
    calc
      _ ≤ ((⌊T⌋₊ / d + 1 : ℕ) : ℝ) := by
        exact_mod_cast card_modEq_row_le ⌊T⌋₊ d n N hN
      _ ≤ (⌊T⌋₊ : ℝ) / d + 1 := by
        push_cast
        gcongr
        exact Nat.cast_div_le
      _ ≤ T / d + 1 := by
        gcongr
        exact Nat.floor_le (by linarith)
      _ ≤ _ := by gcongr
  have he :
      (∑ n ∈ N, ∑ m ∈ N, if Nat.ModEq d n m then β n ^ 2 else 0) = E := by
    simp only [E, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hsym :
      (∑ n ∈ N, ∑ m ∈ N, if Nat.ModEq d n m then β m ^ 2 else 0) = E := by
    rw [sum_comm]
    convert he using 2 with n
    apply sum_congr rfl
    intro m _
    have hc : Nat.ModEq d m n ↔ Nat.ModEq d n m := ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
    simp only [hc]
  calc
    _ ≤ ∑ n ∈ N, ∑ m ∈ N,
        ((if Nat.ModEq d n m then β n ^ 2 else 0) +
          (if Nat.ModEq d n m then β m ^ 2 else 0)) / 2 := by
      rw [sum_product]
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro m _
      dsimp
      split_ifs
      · rw [abs_mul]
        nlinarith [sq_nonneg (|β n| - |β m|), sq_abs (β n), sq_abs (β m)]
      · norm_num
    _ = E := by
      simp only [← sum_div, sum_add_distrib]
      rw [he, hsym]
      ring
    _ ≤ ∑ n ∈ N, β n ^ 2 * (T / Y + 1) := by
      apply sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_left (hrow n) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

/-- A possibly nonsymmetric submask is discarded only after taking
absolute values, leaving the full congruence relation for the energy bound. -/
theorem masked_beta_pair_abs_le_largeDelta
    {T Y : ℝ} (hT : 1 ≤ T) (hY : 0 < Y)
    (N Q : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (β : ℕ → ℝ)
    (a : ℤ) (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ))
    {q r : ℕ} (hq : q ∈ reducedModuli Q a) (hr : r ∈ reducedModuli Q a) :
    |∑ p ∈ N ×ˢ N, if WCompatible q r p.1 p.2 ∧ P ((q, r), p)
      then β p.1 * β p.2 else 0| ≤
      (T / Y + 1) * ∑ n ∈ N, β n ^ 2 := by
  by_cases hδ : Y < (q.gcd r : ℝ)
  · apply le_trans _ (sum_abs_modEq_pairs_le hT hY (q.gcd r) hδ N hN β)
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro p _
    by_cases hc : WCompatible q r p.1 p.2 ∧ P ((q, r), p)
    · simp only [if_pos hc, if_pos hc.1.2.2, le_refl]
    · simp only [if_neg hc, abs_zero]
      split_ifs <;> positivity
  · have hempty (p : ℕ × ℕ) (hp : p ∈ N ×ˢ N) :
        ¬ (WCompatible q r p.1 p.2 ∧ P ((q, r), p)) := by
      intro hc
      exact hδ (hP ((q, r), p)
        (mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hq, hr⟩, hp⟩, hc.1⟩)
        hc.2)
    rw [sum_eq_zero (fun p hp ↦ if_neg (hempty p hp)), abs_zero]
    exact mul_nonneg (by positivity) (sum_nonneg (fun n _ ↦ sq_nonneg (β n)))

/-- Quantitative common-modulus zero-mode bound, with arbitrary signed
beta weights and every further arithmetic submask. The constant is one. -/
theorem wMaskedZeroMode_abs_le_largeDelta_energy
    (j : ℕ) {T L Y : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hY : 0 < Y)
    (M : ℝ) (N Q : Finset ℕ)
    (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) :
    |wMaskedZeroMode M N Q β c a P| ≤
      |M * dyadicCutoffMass| * ((T / Y + 1) * ∑ n ∈ N, β n ^ 2) *
        (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
  let B := (T / Y + 1) * ∑ n ∈ N, β n ^ 2
  have hB : 0 ≤ B := by
    exact mul_nonneg (by positivity) (sum_nonneg (fun n _ ↦ sq_nonneg (β n)))
  rw [wMaskedZeroMode_eq_modulus_sum, abs_mul]
  calc
    _ ≤ |M * dyadicCutoffMass| *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)| * B := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro q hq
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro r hr
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (masked_beta_pair_abs_le_largeDelta hT hY N Q hN β a P hP hq hr)
        (abs_nonneg _)
    _ = |M * dyadicCutoffMass| *
        ((∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)|) * B) := by simp only [sum_mul]
    _ ≤ |M * dyadicCutoffMass| * ((1 + Real.log L) ^ (2 * j ^ 2 + 1) * B) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hB
      exact sum_abs_lcm_weight_le_log j hL (reducedModuli Q a)
        ((filter_subset _ _).trans hQ) c (fun q hq ↦ hc q (mem_filter.mp hq).1)
    _ = _ := by dsimp [B]; ring

/-- Fully evaluated version for beta weights bounded by a divisor function
of positive order. The modulus order may still be zero. -/
theorem wMaskedZeroMode_abs_le_largeDelta
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {T L Y : ℝ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hY : 0 < Y)
    (M : ℝ) (N Q : Finset ℕ)
    (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) :
    |wMaskedZeroMode M N Q β c a P| ≤
      |M * dyadicCutoffMass| * ((T / Y + 1) *
        (T * (1 + Real.log T) ^ (k ^ 2 - 1))) *
          (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
  apply (wMaskedZeroMode_abs_le_largeDelta_energy j hT hL hY
    M N Q hN hQ β c hc a P hP).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith [Real.log_nonneg hL]) _)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (sum_alpha_sq_le_fouvryTau hk hT N hN β hβ) (by positivity)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
