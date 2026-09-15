import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanSW
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDOriginal

/-!
# Divisor deletion at the actual signed-error entry

The equality `m*n=a` is separated before summing modulus divisors.
It costs the total modulus mass once per beta index, not once per alpha index.
All remaining progression terms have a nonzero difference.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem signedError_add_beta (S N Q : Finset ℕ) (α β γ c : ℕ → ℝ) (a : ℤ) :
    signedError S N Q α (fun n => β n + γ n) c a =
      signedError S N Q α β c a + signedError S N Q α γ c a := by
  have hi (P : Prop) [Decidable P] (u v : ℝ) :
      (if P then u + v else 0) =
        (if P then u else 0) + (if P then v else 0) := by
    split_ifs <;> simp
  unfold signedError
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  simp only [bilinearDiscrepancy, mul_add, hi, sum_add_distrib, add_div]
  ring

theorem signedError_eq_clean_add_divisorPart
    (S N Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) :
    signedError S N Q α β c a =
      signedError S N Q α (betaClean β a) c a +
        signedError S N Q α (betaDivisorPart β a) c a := by
  conv_lhs => arg 5; ext n; rw [beta_eq_clean_add_divisorPart β a n]
  exact signedError_add_beta S N Q α _ _ c a

theorem signedError_abs_le_product_majorant
    (S N Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) :
    |signedError S N Q α β c a| ≤
      ∑ n ∈ N, |β n| * ∑ m ∈ S, |α m| *
        ((∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) +
          ∑ q ∈ Q, |c q| / (q.totient : ℝ)) := by
  let F : ℕ → ℝ := fun q =>
    ∑ m ∈ S, ∑ n ∈ N, |α m| * |β n| *
      ((if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) +
        |c q| / (q.totient : ℝ))
  have hF q : 0 ≤ F q := by
    apply sum_nonneg
    intro m _
    apply sum_nonneg
    intro n _
    split_ifs <;> positivity
  calc
    _ ≤ ∑ q ∈ reducedModuli Q a, |c q * bilinearDiscrepancy S N α β a q| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ reducedModuli Q a, F q := by
      apply sum_le_sum
      intro q _
      rw [abs_mul]
      unfold bilinearDiscrepancy
      apply (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)).trans
      rw [mul_add, abs_div,
        abs_of_nonneg (show (0 : ℝ) ≤ q.totient from Nat.cast_nonneg _)]
      have hp : |∑ m ∈ S, ∑ n ∈ N,
          if Int.ModEq q ((m : ℤ) * n) a then α m * β n else 0| ≤
          ∑ m ∈ S, ∑ n ∈ N,
            if Int.ModEq q ((m : ℤ) * n) a then |α m| * |β n| else 0 := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro m _
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro n _
        split_ifs <;> simp [abs_mul]
      have hm : |∑ m ∈ S, ∑ n ∈ N,
          if (m * n).Coprime q then α m * β n else 0| ≤
          ∑ m ∈ S, ∑ n ∈ N, |α m| * |β n| := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro m _
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro n _
        split_ifs <;> simp [abs_mul]; positivity
      apply (add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hm (Nat.cast_nonneg _)) (abs_nonneg _))).trans_eq
      simp only [F, mul_sum, sum_div, ← sum_add_distrib]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      split_ifs <;> ring
    _ ≤ ∑ q ∈ Q, F q :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => hF q)
    _ = _ := by
      dsimp [F]
      rw [sum_comm]
      conv_lhs => arg 2; ext m; rw [sum_comm]
      rw [sum_comm]
      apply sum_congr rfl
      intro n _
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      rw [← mul_sum, ← sum_add_distrib]
      rw [← mul_assoc]
      ring

/-- The equality progression contributes at most one alpha index. -/
theorem sum_progression_moduli_le_split
    (S Q : Finset ℕ) (c : ℕ → ℝ) (a : ℤ) {n : ℕ} (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D)
    (hne : ∀ m ∈ S, (m : ℤ) * n ≠ a →
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ D) :
    (∑ m ∈ S, ∑ q ∈ Q,
        if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤
      (S.card : ℝ) * D + ∑ q ∈ Q, |c q| := by
  let E := S.filter (fun m : ℕ => (m : ℤ) * n = a)
  have hcard : E.card ≤ 1 := by
    apply card_le_one.mpr
    intro m hm r hr
    have he := (mem_filter.mp hm).2
    have he' := (mem_filter.mp hr).2
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    exact_mod_cast mul_right_cancel₀ hn' (he.trans he'.symm)
  have hsumE : (∑ m ∈ S, if (m : ℤ) * n = a then ∑ q ∈ Q, |c q| else 0) ≤
      ∑ q ∈ Q, |c q| := by
    have hh : (∑ _m ∈ E, ∑ q ∈ Q, |c q|) ≤ ∑ q ∈ Q, |c q| := by
      simp only [sum_const, nsmul_eq_mul]
      exact mul_le_of_le_one_left (sum_nonneg (fun _ _ => abs_nonneg _))
        (by exact_mod_cast hcard)
    simpa only [E, sum_filter] using hh
  calc
    _ ≤ ∑ m ∈ S, (D + if (m : ℤ) * n = a then ∑ q ∈ Q, |c q| else 0) := by
      apply sum_le_sum
      intro m hm
      by_cases he : (m : ℤ) * n = a
      · simp only [he, Int.ModEq.refl, ite_true]
        linarith
      · simpa only [if_neg he, add_zero] using hne m hm he
    _ = (S.card : ℝ) * D +
        ∑ m ∈ S, if (m : ℤ) * n = a then ∑ q ∈ Q, |c q| else 0 := by
      rw [sum_add_distrib]; simp
    _ ≤ _ := add_le_add le_rfl hsumE

/-- A finite majorant retaining the separate equality cost. -/
theorem signedError_abs_le_split
    (S N Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hα : ∀ m ∈ S, |α m| ≤ A)
    (hN : ∀ n ∈ N, 0 < n)
    (hne : ∀ n ∈ N, ∀ m ∈ S, (m : ℤ) * n ≠ a →
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ D) :
    |signedError S N Q α β c a| ≤
      A * (∑ n ∈ N, |β n|) *
        ((S.card : ℝ) * D + ∑ q ∈ Q, |c q| +
          (S.card : ℝ) * ∑ q ∈ Q, |c q| / (q.totient : ℝ)) := by
  apply (signedError_abs_le_product_majorant S N Q α β c a).trans
  rw [show A * (∑ n ∈ N, |β n|) *
      ((S.card : ℝ) * D + ∑ q ∈ Q, |c q| +
        (S.card : ℝ) * ∑ q ∈ Q, |c q| / (q.totient : ℝ)) =
      ∑ n ∈ N, A * |β n| *
        ((S.card : ℝ) * D + ∑ q ∈ Q, |c q| +
          (S.card : ℝ) * ∑ q ∈ Q, |c q| / (q.totient : ℝ)) by
    rw [mul_sum, sum_mul]]
  apply sum_le_sum
  intro n hn
  have hb := sum_progression_moduli_le_split S Q c a (hN n hn) hD (hne n hn)
  calc
    _ ≤ |β n| * ∑ m ∈ S, A *
        ((∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) +
          ∑ q ∈ Q, |c q| / (q.totient : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_right (hα m hm)
      apply add_nonneg
      · apply sum_nonneg; intro q _; split_ifs <;> positivity
      · positivity
    _ = |β n| * A *
        ((∑ m ∈ S, ∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) +
          (S.card : ℝ) * ∑ q ∈ Q, |c q| / (q.totient : ℝ)) := by
      simp only [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    _ ≤ |β n| * A *
        ((S.card : ℝ) * D + ∑ q ∈ Q, |c q| +
          (S.card : ℝ) * ∑ q ∈ Q, |c q| / (q.totient : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) (mul_nonneg (abs_nonneg _) hA)
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
