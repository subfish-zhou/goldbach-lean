import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmallDelta

/-!
# The very-large-gcd endpoint of the actual zero-mode covariance

When the gcd exceeds the beta support endpoint, each residue class contains
at most one supported integer. Centering is an orthogonal projection, so
the covariance is bounded by the beta square sum without any AP hypothesis.
This does not estimate the intermediate gcd range.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

theorem betaResidueMass_sq_eq_highDelta
    (N : Finset ℕ) (β : ℕ → ℝ) (q δ b : ℕ)
    (hN : ∀ n ∈ N, n < δ) :
    betaResidueMass N β q δ b ^ 2 =
      betaResidueMass N (fun n => β n ^ 2) q δ b := by
  classical
  by_cases hex : ∃ n ∈ N, n.Coprime q ∧ Nat.ModEq δ n b
  · obtain ⟨n, hn, hc⟩ := hex
    have hu : ∀ m ∈ N, m ≠ n → ¬(m.Coprime q ∧ Nat.ModEq δ m b) := by
      intro m hm hne h
      have he := h.2.trans hc.2.symm
      simp only [Nat.ModEq, Nat.mod_eq_of_lt (hN m hm),
        Nat.mod_eq_of_lt (hN n hn)] at he
      exact hne he
    unfold betaResidueMass
    rw [sum_eq_single n, sum_eq_single n]
    · simp [hc]
    · intro m hm hne
      exact if_neg (hu m hm hne)
    · exact fun h => (h hn).elim
    · intro m hm hne
      exact if_neg (hu m hm hne)
    · exact fun h => (h hn).elim
  · have hz (γ : ℕ → ℝ) : betaResidueMass N γ q δ b = 0 := by
      apply sum_eq_zero
      intro n hn
      exact if_neg (fun h => hex ⟨n, hn, h⟩)
    rw [hz β, hz (fun n => β n ^ 2)]
    norm_num

/-- The centered energy is at most the original beta energy, with the
actual coprime sieve and the canonical reduced classes retained. -/
theorem sum_betaResidueMass_centered_sq_le_highDelta
    (N : Finset ℕ) (β : ℕ → ℝ) {q δ : ℕ}
    (hδ : 0 < δ) (hdq : δ ∣ q) (hN : ∀ n ∈ N, n < δ) :
    (∑ b ∈ betaReducedResidues δ,
      (betaResidueMass N β q δ b - coprimeMass N β q / (δ.totient : ℝ)) ^ 2) ≤
        ∑ n ∈ N, β n ^ 2 := by
  have hφ : (δ.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hδ).ne'
  have he :
      (∑ b ∈ betaReducedResidues δ,
        (betaResidueMass N β q δ b - coprimeMass N β q / (δ.totient : ℝ)) ^ 2) =
      (∑ b ∈ betaReducedResidues δ, betaResidueMass N β q δ b ^ 2) -
        coprimeMass N β q ^ 2 / (δ.totient : ℝ) := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      ← sum_mul, sum_const, nsmul_eq_mul, betaReducedResidues_card,
      sum_betaResidueMass N β hδ hdq]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ ∑ b ∈ betaReducedResidues δ, betaResidueMass N β q δ b ^ 2 :=
      sub_le_self _ (by positivity)
    _ = coprimeMass N (fun n => β n ^ 2) q := by
      simp_rw [betaResidueMass_sq_eq_highDelta N β q δ _ hN]
      exact sum_betaResidueMass N _ hδ hdq
    _ ≤ _ := by
      apply sum_le_sum
      intro n _
      change (if n.Coprime q then β n ^ 2 else 0) ≤ β n ^ 2
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _

/-- No progression estimate is needed once the gcd exceeds the support. -/
theorem betaCovariance_abs_le_highDelta
    {T : ℝ} (hT : 0 ≤ T) (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊)
    (β : ℕ → ℝ) {q r : ℕ} (hδ : T < (q.gcd r : ℝ)) :
    |betaCovariance N β q r| ≤ ∑ n ∈ N, β n ^ 2 := by
  have hd : 0 < q.gcd r := by exact_mod_cast lt_of_le_of_lt hT hδ
  have hn : ∀ n ∈ N, n < q.gcd r := by
    intro n hn
    have hle : (n : ℝ) ≤ T :=
      (Nat.cast_le.mpr (mem_Ioc.mp (hN hn)).2).trans (Nat.floor_le hT)
    exact_mod_cast lt_of_le_of_lt hle hδ
  have hq := sum_betaResidueMass_centered_sq_le_highDelta N β hd
    (Nat.gcd_dvd_left q r) hn
  have hr := sum_betaResidueMass_centered_sq_le_highDelta N β hd
    (Nat.gcd_dvd_right q r) hn
  unfold betaCovariance
  calc
    _ ≤ ∑ b ∈ betaReducedResidues (q.gcd r),
        ((betaResidueMass N β q (q.gcd r) b -
            coprimeMass N β q / ((q.gcd r).totient : ℝ)) ^ 2 +
         (betaResidueMass N β r (q.gcd r) b -
            coprimeMass N β r / ((q.gcd r).totient : ℝ)) ^ 2) / 2 := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b _
      rw [abs_mul]
      nlinarith [sq_nonneg
        (|betaResidueMass N β q (q.gcd r) b -
            coprimeMass N β q / ((q.gcd r).totient : ℝ)| -
         |betaResidueMass N β r (q.gcd r) b -
            coprimeMass N β r / ((q.gcd r).totient : ℝ)|),
        sq_abs (betaResidueMass N β q (q.gcd r) b -
            coprimeMass N β q / ((q.gcd r).totient : ℝ)),
        sq_abs (betaResidueMass N β r (q.gcd r) b -
            coprimeMass N β r / ((q.gcd r).totient : ℝ))]
    _ ≤ _ := by rw [← sum_div, sum_add_distrib]; linarith

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
