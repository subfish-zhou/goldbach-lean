import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPrimePrefix

/-! The nonprincipal carrier required by the first line of Pan (2.4), and the
literal bad-prime correction used in (2.12).  The existing `panIymLow` is not
changed and is not asserted to be small. -/
namespace AnalyticNumberTheory.LargeSieve.PanLow
open Classical Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- Puncture the principal character before applying SW. -/
def nonprincipalPrimitiveCharacters (q : ℕ) : Finset (PrimitiveCharacter q) :=
  univ.filter (fun χ => χ.1 ≠ 1)

/-- Pan's whole-a norm on the explicitly nonprincipal low carrier. -/
def nonprincipalLow (g d : ℕ → ℂ) (N A₁ A₂ Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (q.totient : ℝ)⁻¹ *
    ∑ χ ∈ nonprincipalPrimitiveCharacters q,
      ‖panSourceCharacterAmplitude g d N A₁ A₂ χ‖

@[simp] theorem nonprincipalPrimitiveCharacters_one : nonprincipalPrimitiveCharacters 1 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro χ hχ
  have he : χ.1 = 1 := by
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    simp
  exact (mem_filter.mp hχ).2 he

theorem nonprincipalPrimitiveCharacters_eq_univ {q : ℕ} (hq : 2 ≤ q) :
    nonprincipalPrimitiveCharacters q = univ := by
  ext χ
  simp only [nonprincipalPrimitiveCharacters, mem_filter, mem_univ, true_and]
  exact iff_true_intro (primitiveCharacter_ne_one_of_two_le hq χ)

/-- Primitivity eliminates principal characters for q ≥ 2; q = 1 disappears,
not by an SW estimate but because its explicitly nonprincipal carrier is empty. -/
theorem nonprincipalLow_eq_two_le (g d : ℕ → ℂ) (N A₁ A₂ Q : ℕ) :
    nonprincipalLow g d N A₁ A₂ Q =
      ∑ q ∈ Icc 2 Q, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q, ‖panSourceCharacterAmplitude g d N A₁ A₂ χ‖ := by
  unfold nonprincipalLow
  calc
    _ = ∑ q ∈ Icc 2 Q, (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ nonprincipalPrimitiveCharacters q,
          ‖panSourceCharacterAmplitude g d N A₁ A₂ χ‖ := by
      symm
      apply sum_subset
      · exact Icc_subset_Icc_left (by omega)
      · intro q hq hn
        have hq1 : q = 1 := by simp only [mem_Icc] at hq hn; omega
        subst q
        simp
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      rw [nonprincipalPrimitiveCharacters_eq_univ (mem_Icc.mp hq).1]

/-- The actual prime prefix with the restriction (n,m)=1. -/
def coprimePrimePrefix {q : ℕ} (χ : DirichletCharacter ℂ q) (y m : ℕ) : ℂ :=
  ∑ n ∈ range (y + 1), if n.Prime ∧ n.Coprime m then χ (n : ZMod q) else 0

/-- Exactly the discarded primes dividing m, not a von Mangoldt surrogate. -/
theorem primePrefix_sub_coprimePrimePrefix {q : ℕ}
    (χ : DirichletCharacter ℂ q) (y m : ℕ) :
    primePrefix χ y - coprimePrimePrefix χ y m =
      ∑ n ∈ (range (y + 1)).filter (fun n => n.Prime ∧ ¬ n.Coprime m),
        χ (n : ZMod q) := by
  simp only [primePrefix, coprimePrimePrefix, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · rw [if_pos hp]
    by_cases hc : n.Coprime m
    · rw [if_pos ⟨hp, hc⟩, if_neg (by tauto : ¬ (n.Prime ∧ ¬ n.Coprime m))]
      exact sub_self _
    · rw [if_neg (by tauto : ¬ (n.Prime ∧ n.Coprime m)), if_pos ⟨hp, hc⟩, sub_zero]
  · rw [if_neg hp, if_neg (by tauto : ¬ (n.Prime ∧ n.Coprime m)),
      if_neg (by tauto : ¬ (n.Prime ∧ ¬ n.Coprime m)), sub_self]

/-- Uniform bad-prime bound by omega(m).  The positive-m hypothesis is essential. -/
theorem norm_primePrefix_sub_coprimePrimePrefix_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (y m : ℕ) (hm : 0 < m) :
    ‖primePrefix χ y - coprimePrimePrefix χ y m‖ ≤ (m.primeFactors.card : ℝ) := by
  rw [primePrefix_sub_coprimePrimePrefix]
  calc
    _ ≤ ∑ n ∈ (range (y + 1)).filter (fun n => n.Prime ∧ ¬ n.Coprime m),
        ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ (range (y + 1)).filter (fun n => n.Prime ∧ ¬ n.Coprime m), (1 : ℝ) :=
      sum_le_sum fun n _ => χ.norm_le_one _
    _ ≤ (m.primeFactors.card : ℝ) := by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_le_card (show
        (range (y + 1)).filter (fun n => n.Prime ∧ ¬ n.Coprime m) ⊆ m.primeFactors from by
          intro n hn
          rcases (mem_filter.mp hn).2 with ⟨hp, hc⟩
          exact Nat.mem_primeFactors.mpr ⟨hp, not_not.mp
            (by simpa only [hp.coprime_iff_not_dvd] using hc), hm.ne'⟩)

/-- Existing arithmetic count makes the correction at most log₂(m). -/
theorem norm_primePrefix_sub_coprimePrimePrefix_le_log2 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (y m : ℕ) (hm : 0 < m) :
    ‖primePrefix χ y - coprimePrimePrefix χ y m‖ ≤ (Nat.log2 m : ℝ) :=
  (norm_primePrefix_sub_coprimePrimePrefix_le χ y m hm).trans
    (by exact_mod_cast card_primeFactors_le_log2 hm)

/-- The same actual prime indicator in the Icc normalization used by Pan. -/
theorem coprimePrimePrefix_eq_Icc {q : ℕ}
    (χ : DirichletCharacter ℂ q) (y m : ℕ) :
    coprimePrimePrefix χ y m =
      ∑ n ∈ Icc 1 y, (if n.Prime ∧ n.Coprime m then (1 : ℂ) else 0) *
        χ (n : ZMod q) := by
  have hr : range (y + 1) = insert 0 (Icc 1 y) := by
    ext n
    simp
    omega
  unfold coprimePrimePrefix
  rw [hr, sum_insert (by simp)]
  simp only [Nat.not_prime_zero, false_and, ite_false, zero_add]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

/-- The unrestricted actual prime coefficient in Pan's Icc normalization. -/
theorem primePrefix_eq_Icc {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℕ) :
    primePrefix χ y =
      ∑ n ∈ Icc 1 y, (if n.Prime then (1 : ℂ) else 0) * χ (n : ZMod q) := by
  have he : primePrefix χ y = coprimePrimePrefix χ y 1 := by
    simp [primePrefix, coprimePrimePrefix]
  rw [he, coprimePrimePrefix_eq_Icc]
  simp

/-- Whole-a norm retained; the triangle inequality is used only for paying the
low-conductor bad-prime correction.  No high-conductor estimate is claimed. -/
theorem source_prime_coprime_difference_le
    (g : ℕ → ℂ) (N A₁ A₂ m : ℕ) (hm : 0 < m)
    (hg : ∀ a ∈ Ioc A₁ A₂, ‖g a‖ ≤ 1) {q : ℕ} (χ : PrimitiveCharacter q) :
    ‖(∑ a ∈ Ioc A₁ A₂, g a * χ.1 (a : ZMod q) * primePrefix χ.1 (N / a)) -
      panSourceCharacterAmplitude g
        (fun n => if n.Prime ∧ n.Coprime m then 1 else 0) N A₁ A₂ χ‖ ≤
      ((Ioc A₁ A₂).card : ℝ) * (m.primeFactors.card : ℝ) := by
  have hid : panSourceCharacterAmplitude g
      (fun n => if n.Prime ∧ n.Coprime m then 1 else 0) N A₁ A₂ χ =
      ∑ a ∈ Ioc A₁ A₂, g a * χ.1 (a : ZMod q) * coprimePrimePrefix χ.1 (N / a) m := by
    simp only [panSourceCharacterAmplitude, coprimePrimePrefix_eq_Icc]
  rw [hid, ← sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ Ioc A₁ A₂,
        ‖g a * χ.1 (a : ZMod q) * primePrefix χ.1 (N / a) -
          g a * χ.1 (a : ZMod q) * coprimePrimePrefix χ.1 (N / a) m‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Ioc A₁ A₂, (m.primeFactors.card : ℝ) := by
      apply sum_le_sum
      intro a ha
      rw [← mul_sub, norm_mul]
      have hcoeff : ‖g a * χ.1 (a : ZMod q)‖ ≤ 1 := by
        rw [norm_mul]
        exact (mul_le_mul (hg a ha) (χ.1.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul 1)
      exact (mul_le_mul hcoeff (norm_primePrefix_sub_coprimePrimePrefix_le χ.1 (N / a) m hm)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp
end
end AnalyticNumberTheory.LargeSieve.PanLow