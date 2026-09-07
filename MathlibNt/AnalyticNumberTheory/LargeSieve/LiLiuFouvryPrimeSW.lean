import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmallDeltaPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418Unconditional
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPrimePrefix

/-! Concrete prime intervals and the exact support of the independent sieve loss. -/
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Finset
noncomputable section

def primeSWBeta (n : ℕ) : ℝ := if n.Prime then 1 else 0

def primeSWInterval (u v : ℝ) : Finset ℕ := Ioc ⌊u⌋₊ ⌊v⌋₊

/-- The independent sieve deletes only prime divisors of its own modulus. -/
theorem primeSW_deleted_subset (N : Finset ℕ) {h : ℕ} (hh : h ≠ 0) :
    N.filter (fun n => n.Prime ∧ ¬n.Coprime h) ⊆ h.primeFactors := by
  intro p hp
  obtain ⟨_, hp, hcop⟩ := mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp, hp.dvd_iff_not_coprime.mpr hcop, hh⟩

/-- The loss count is uniform in the interval and in the progression. -/
theorem primeSW_deleted_card_le (N : Finset ℕ) {h : ℕ} (hh : h ≠ 0) :
    (N.filter (fun n => n.Prime ∧ ¬n.Coprime h)).card ≤ h.primeFactors.card :=
  card_le_card (primeSW_deleted_subset N hh)

/-- The literal prime coefficient, without an additional coprimality mask. -/
theorem primeSWBeta_nonneg (n : ℕ) : 0 ≤ primeSWBeta n := by
  unfold primeSWBeta
  split_ifs <;> norm_num

/-- The loss is absorbed by the fixed second divisor function. -/
theorem primeSW_primeFactors_le_tau (h : ℕ) : h.primeFactors.card ≤ fouvryTau 2 h := by
  rw [fouvryTau_two]
  apply card_le_card
  intro p hp
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp,
    (Nat.mem_primeFactors.mp hp).2.2⟩

/-- Prime mass subject to a literal predicate. -/
def primeSWSum (N : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  ∑ n ∈ N, if P n then primeSWBeta n else 0

theorem primeSWSum_eq_card (N : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    primeSWSum N P = ((N.filter (fun n => n.Prime ∧ P n)).card : ℝ) := by
  simp only [primeSWSum, primeSWBeta, ← sum_boole]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp_all

theorem primeSWSum_nonneg (N : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    0 ≤ primeSWSum N P := by rw [primeSWSum_eq_card]; positivity

/-- Exact deletion identity; the same predicate occurs on both sides. -/
theorem primeSWSum_sieve_sub (N : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ℕ) :
    primeSWSum N (fun n => P n ∧ n.Coprime h) - primeSWSum N P =
      -primeSWSum N (fun n => P n ∧ ¬n.Coprime h) := by
  unfold primeSWSum
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n _
  by_cases hp : P n
  · simp only [hp, true_and, if_true]
    by_cases hc : n.Coprime h
    · rw [if_pos hc, if_neg (not_not.mpr hc)]
      ring
    · rw [if_neg hc, if_pos hc]
      ring
  · simp only [hp, false_and, if_false, sub_self, neg_zero]

/-- Uniform sieve perturbation for every predicate, not an SW assertion for subsets. -/
theorem primeSWSum_sieve_abs_sub_le (N : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] {h : ℕ} (hh : h ≠ 0) :
    |primeSWSum N (fun n => P n ∧ n.Coprime h) - primeSWSum N P| ≤
      (fouvryTau 2 h : ℝ) := by
  rw [primeSWSum_sieve_sub, abs_neg, abs_of_nonneg (primeSWSum_nonneg _ _),
    primeSWSum_eq_card]
  exact_mod_cast (card_le_card (show
    N.filter (fun n => n.Prime ∧ (P n ∧ ¬n.Coprime h)) ⊆
      N.filter (fun n => n.Prime ∧ ¬n.Coprime h) from by
    intro n hn
    obtain ⟨hn, hp, _, hc⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hn, hp, hc⟩)).trans
      ((primeSW_deleted_card_le N hh).trans (primeSW_primeFactors_le_tau h))

/-- The totient denominator in the centering term is retained explicitly. -/
theorem primeSW_sieve_discrepancy_sub_le (N : Finset ℕ) {d h : ℕ}
    (hd : 0 < d) (hh : 0 < h) (b : ℕ) :
    |betaCoprimeAPDiscrepancy N primeSWBeta d h b -
      betaCoprimeAPDiscrepancy N primeSWBeta d 1 b| ≤
        2 * (fouvryTau 2 h : ℝ) := by
  have hφ : (1 : ℝ) ≤ d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφ0 : (0 : ℝ) < d.totient := lt_of_lt_of_le zero_lt_one hφ
  have hAP := primeSWSum_sieve_abs_sub_le N (fun n => Nat.ModEq d n b) hh.ne'
  have hmass := primeSWSum_sieve_abs_sub_le N (fun n => n.Coprime d) hh.ne'
  have he : betaCoprimeAPDiscrepancy N primeSWBeta d h b -
      betaCoprimeAPDiscrepancy N primeSWBeta d 1 b =
      (primeSWSum N (fun n => Nat.ModEq d n b ∧ n.Coprime h) -
        primeSWSum N (fun n => Nat.ModEq d n b)) -
      (primeSWSum N (fun n => n.Coprime d ∧ n.Coprime h) -
        primeSWSum N (fun n => n.Coprime d)) / d.totient := by
    simp only [betaCoprimeAPDiscrepancy, coprimeMass, primeSWSum,
      Nat.coprime_mul_iff_right, mul_one, and_comm]
    simp only [Nat.coprime_one_right_eq_true, and_true]
    ring
  rw [he]
  calc
    _ ≤ |primeSWSum N (fun n => Nat.ModEq d n b ∧ n.Coprime h) -
        primeSWSum N (fun n => Nat.ModEq d n b)| +
      |primeSWSum N (fun n => n.Coprime d ∧ n.Coprime h) -
        primeSWSum N (fun n => n.Coprime d)| / d.totient := by
      calc
        _ ≤ |primeSWSum N (fun n => Nat.ModEq d n b ∧ n.Coprime h) -
            primeSWSum N (fun n => Nat.ModEq d n b)| +
          |(primeSWSum N (fun n => n.Coprime d ∧ n.Coprime h) -
            primeSWSum N (fun n => n.Coprime d)) / d.totient| := abs_sub _ _
        _ = _ := by rw [abs_div, Nat.abs_cast]
    _ ≤ (fouvryTau 2 h : ℝ) + (fouvryTau 2 h : ℝ) / d.totient :=
      add_le_add hAP (div_le_div_of_nonneg_right hmass hφ0.le)
    _ ≤ _ := by have := div_le_self (Nat.cast_nonneg (fouvryTau 2 h)) hφ; linarith

/-- The modulus-one endpoint vanishes even with the independent sieve. -/
theorem primeSW_discrepancy_one (N : Finset ℕ) (h b : ℕ) :
    betaCoprimeAPDiscrepancy N primeSWBeta 1 h b = 0 := by
  simp only [betaCoprimeAPDiscrepancy, coprimeMass, Nat.ModEq, Nat.mod_one,
    and_true, one_mul, Nat.totient_one, Nat.cast_one, div_one, sub_self]

/-- A predicate can only decrease the literal prime mass. -/
theorem primeSWSum_mono (N M : Finset ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hNM : N ⊆ M)
    (hPQ : ∀ n ∈ N, P n → Q n) : primeSWSum N P ≤ primeSWSum M Q := by
  rw [primeSWSum_eq_card, primeSWSum_eq_card]
  exact_mod_cast card_le_card (show N.filter (fun n => n.Prime ∧ P n) ⊆
    M.filter (fun n => n.Prime ∧ Q n) from by
    intro n hn
    obtain ⟨hn, hp, hP⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hNM hn, hp, hPQ n hn hP⟩)

/-- The original discrepancy, expressed with literal prime masses. -/
theorem primeSW_discrepancy_eq (N : Finset ℕ) (d h b : ℕ) :
    betaCoprimeAPDiscrepancy N primeSWBeta d h b =
      primeSWSum N (fun n => n.Coprime h ∧ Nat.ModEq d n b) -
        primeSWSum N (fun n => n.Coprime (d * h)) / d.totient := rfl

/-- Absolute mass never exceeds the number of available integers. -/
theorem primeSWSum_le_card (N : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    primeSWSum N P ≤ (N.card : ℝ) := by
  rw [primeSWSum_eq_card]
  exact_mod_cast card_le_card (filter_subset _ _)

/-- A bounded-scale bound, valid also for modulus one and empty intervals. -/
theorem primeSW_discrepancy_le_card (N : Finset ℕ) {d : ℕ} (hd : 0 < d)
    (h b : ℕ) : |betaCoprimeAPDiscrepancy N primeSWBeta d h b| ≤ 2 * N.card := by
  rw [primeSW_discrepancy_eq]
  have hφ : (1 : ℝ) ≤ d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφ0 : (0 : ℝ) ≤ d.totient := Nat.cast_nonneg _
  calc
    _ ≤ primeSWSum N (fun n => n.Coprime h ∧ Nat.ModEq d n b) +
        primeSWSum N (fun n => n.Coprime (d * h)) / d.totient := by
      simpa only [abs_of_nonneg (primeSWSum_nonneg _ _),
        abs_of_nonneg (div_nonneg (primeSWSum_nonneg _ _) hφ0)] using
        abs_sub (primeSWSum N (fun n => n.Coprime h ∧ Nat.ModEq d n b))
          (primeSWSum N (fun n => n.Coprime (d * h)) / d.totient)
    _ ≤ (N.card : ℝ) + (N.card : ℝ) / d.totient :=
      add_le_add (primeSWSum_le_card _ _)
        (div_le_div_of_nonneg_right (primeSWSum_le_card _ _) hφ0)
    _ ≤ _ := by have := div_le_self (Nat.cast_nonneg N.card) hφ; linarith

end
end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
