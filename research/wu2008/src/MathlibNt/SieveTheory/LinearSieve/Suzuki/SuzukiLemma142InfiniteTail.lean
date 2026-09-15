import MathlibNt.SieveTheory.SwitchingPrinciple

open scoped BigOperators

namespace MathlibNt.SieveTheory

/-- Suzuki's Lemma 14.2: bounds for the infinite exponential tail. -/
theorem suzuki_lemma14_2_infinite_tail
    (x : ℝ) (M : ℕ) (hx : 0 ≤ x) :
    x ^ M / M.factorial ≤
        (∑' n : ℕ, if M ≤ n then x ^ n / n.factorial else 0) ∧
      (∑' n : ℕ, if M ≤ n then x ^ n / n.factorial else 0) ≤
        x ^ M / M.factorial * Real.exp x := by
  let term : ℕ → ℝ := fun n => x ^ n / n.factorial
  let s : Set ℕ := {n | M ≤ n}
  let e : ℕ ≃ s :=
    { toFun := fun k => ⟨M + k, Nat.le_add_right M k⟩
      invFun := fun n => n.1 - M
      left_inv := by
        intro k
        simp
      right_inv := by
        intro n
        apply Subtype.ext
        exact Nat.add_sub_of_le n.2 }
  have htail :
      (∑' n : ℕ, if M ≤ n then term n else 0) =
        ∑' k : ℕ, term (M + k) := by
    calc
      (∑' n : ℕ, if M ≤ n then term n else 0) =
          ∑' n : ℕ, s.indicator term n := by
            congr 1
            funext n
            classical
            by_cases h : M ≤ n <;> simp [s, h]
      _ = ∑' n : s, term n := (tsum_subtype s term).symm
      _ = ∑' k : ℕ, term (e k) :=
        (e.tsum_eq (fun n : s => term n.1)).symm
      _ = ∑' k : ℕ, term (M + k) := by
        congr 1
  have hterm : Summable term := Real.summable_pow_div_factorial x
  have hshift : Summable (fun k : ℕ => term (M + k)) :=
    hterm.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hfactorial (k : ℕ) :
      (M.factorial : ℝ) * k.factorial ≤ (M + k).factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (M + k))
      (Nat.factorial_mul_factorial_dvd_factorial_add M k)
  have hpoint (k : ℕ) :
      term (M + k) ≤ (x ^ M / M.factorial) * (x ^ k / k.factorial) := by
    change x ^ (M + k) / (M + k).factorial ≤
      (x ^ M / M.factorial) * (x ^ k / k.factorial)
    rw [pow_add, div_mul_div_comm]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (M + k).factorial)
      (by positivity : (0 : ℝ) < M.factorial * k.factorial)).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hfactorial k)
        (mul_nonneg (pow_nonneg hx M) (pow_nonneg hx k))
  have hexp : HasSum (fun k : ℕ => x ^ k / k.factorial) (Real.exp x) := by
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp x)
  have hscaled :
      HasSum (fun k : ℕ => (x ^ M / M.factorial) * (x ^ k / k.factorial))
        (x ^ M / M.factorial * Real.exp x) :=
    hexp.mul_left (x ^ M / M.factorial)
  constructor
  · rw [show (∑' n : ℕ, if M ≤ n then x ^ n / n.factorial else 0) =
        ∑' k : ℕ, term (M + k) by simpa [term] using htail]
    simpa [term] using
      hshift.le_tsum 0 (fun k hk => by positivity)
  · rw [show (∑' n : ℕ, if M ≤ n then x ^ n / n.factorial else 0) =
        ∑' k : ℕ, term (M + k) by simpa [term] using htail]
    calc
      (∑' k : ℕ, term (M + k)) ≤
          ∑' k : ℕ, (x ^ M / M.factorial) * (x ^ k / k.factorial) :=
        hshift.tsum_le_tsum hpoint hscaled.summable
      _ = x ^ M / M.factorial * Real.exp x := hscaled.tsum_eq

end MathlibNt.SieveTheory
