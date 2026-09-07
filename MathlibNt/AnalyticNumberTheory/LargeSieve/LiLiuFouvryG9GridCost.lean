import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridCarrier

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- A real logarithmic bound for the number of actually occupied grid cells. -/
theorem fouvryG9GridCost_card {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    (hN : 1 ≤ Real.log (N : ℝ)) :
    ((fouvryG9GridUsed N eps ρ).card : ℝ) ≤
      (1 / Real.log ρ + 1) ^ 3 * Real.log (N : ℝ) ^ 3 := by
  have hr : 0 < Real.log ρ := Real.log_pos hρ
  have hf : (fouvryG9GridIndex ρ N : ℝ) ≤ Real.log (N : ℝ) / Real.log ρ := by
    unfold fouvryG9GridIndex
    exact Nat.floor_le (div_nonneg (by linarith) hr.le)
  have hb : (fouvryG9GridIndex ρ N : ℝ) + 1 ≤
      (1 / Real.log ρ + 1) * Real.log (N : ℝ) := by
    calc
      _ ≤ Real.log (N : ℝ) / Real.log ρ + Real.log (N : ℝ) := add_le_add hf hN
      _ = _ := by ring
  have hc : ((fouvryG9GridUsed N eps ρ).card : ℝ) ≤
      ((fouvryG9GridIndex ρ N : ℝ) + 1) ^ 3 := by
    exact_mod_cast fouvryG9GridUsed_card_le (N := N) (eps := eps) hρ
  calc
    _ ≤ ((fouvryG9GridIndex ρ N : ℝ) + 1) ^ 3 := hc
    _ ≤ ((1 / Real.log ρ + 1) * Real.log (N : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hb 3
    _ = _ := by ring

/-- The local logarithm comparison is uniform on the full window, including x < N. -/
theorem fouvryG9GridCost_log_window {n K x : ℝ} (hK : 1 ≤ K)
    (hn : 0 < n)
    (hlarge : 2 * Real.log K ≤ Real.log n) (hx : n / K ≤ x) :
    0 < x ∧ Real.log n / 2 ≤ Real.log x := by
  have hKpos : 0 < K := by linarith
  have hlower : 0 < n / K := div_pos hn hKpos
  have hmono := Real.log_le_log hlower hx
  rw [Real.log_div (ne_of_gt hn) (ne_of_gt hKpos)] at hmono
  exact ⟨lt_of_lt_of_le hlower hx, by linarith⟩

/-- One C2-sized real error costs a fixed multiple of N / log(N)^(A+4). -/
theorem fouvryG9GridCost_one {n K x E : ℝ} (A : ℕ) (hK : 1 ≤ K)
    (hn : 0 < n) (hlog : 1 ≤ Real.log n)
    (hlarge : 2 * Real.log K ≤ Real.log n)
    (hxlo : n / K ≤ x) (hxhi : x ≤ 4 * n)
    (hE : |E| ≤ x / Real.log x ^ (A + 4)) :
    |E| ≤ (4 * 2 ^ (A + 4)) * n / Real.log n ^ (A + 4) := by
  obtain ⟨hxpos, hxlog⟩ := fouvryG9GridCost_log_window hK hn hlarge hxlo
  have hln : 0 < Real.log n := by linarith
  have hlx : 0 < Real.log x := by linarith
  have hp : Real.log n ^ (A + 4) ≤
      2 ^ (A + 4) * Real.log x ^ (A + 4) := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ hln.le (show Real.log n ≤ 2 * Real.log x by linarith) (A + 4)
  apply hE.trans
  apply (div_le_div_iff₀ (pow_pos hlx _) (pow_pos hln _)).2
  calc
    x * Real.log n ^ (A + 4) ≤ (4 * n) *
        (2 ^ (A + 4) * Real.log x ^ (A + 4)) :=
      mul_le_mul hxhi hp (by positivity) (by positivity)
    _ = _ := by ring

/-- Exact payment of the cubic grid cost with the last spare logarithmic power. -/
theorem fouvryG9GridCost_scalar {n D C : ℝ} (A : ℕ)
    (hn : 0 ≤ n) (hl : 0 < Real.log n) (hDC : D * C ≤ Real.log n) :
    (D * Real.log n ^ 3) * (C * n / Real.log n ^ (A + 4)) ≤
      n / Real.log n ^ A := by
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hl _) (pow_pos hl _)).2
  have h := mul_le_mul_of_nonneg_right hDC
    (show 0 ≤ n * Real.log n ^ 3 * Real.log n ^ A by positivity)
  convert h using 1 <;> (try simp only [pow_add]) <;> ring

/-- The actual occupied grid pays all local C2 envelopes, uniformly in eps and every scale. -/
theorem fouvryG9GridCost_total (ρ K : ℝ) (A : ℕ) (hρ : 1 < ρ) (hK : 1 ≤ K) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ eps : ℝ,
      ∀ x E : (ℕ × ℕ × ℕ) → ℝ,
        (∀ k ∈ fouvryG9GridUsed N eps ρ, (N : ℝ) / K ≤ x k ∧ x k ≤ 4 * N) →
        (∀ k ∈ fouvryG9GridUsed N eps ρ,
          |E k| ≤ x k / Real.log (x k) ^ (A + 4)) →
        ∑ k ∈ fouvryG9GridUsed N eps ρ, |E k| ≤ (N : ℝ) / Real.log (N : ℝ) ^ A := by
  let D : ℝ := (1 / Real.log ρ + 1) ^ 3
  let C : ℝ := 4 * 2 ^ (A + 4)
  let L : ℝ := max 1 (max (2 * Real.log K) (D * C))
  refine ⟨Real.exp L, ?_⟩
  intro N hN eps x E hx hE
  have hn : 0 < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos L) hN
  have hL : L ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hn).2 hN
  have hlog : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL
  have hlarge : 2 * Real.log K ≤ Real.log (N : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hL
  have hDC : D * C ≤ Real.log (N : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hL
  have hlocal : ∀ k ∈ fouvryG9GridUsed N eps ρ,
      |E k| ≤ C * N / Real.log (N : ℝ) ^ (A + 4) := by
    intro k hk
    exact fouvryG9GridCost_one A hK hn hlog hlarge (hx k hk).1 (hx k hk).2 (hE k hk)
  calc
    _ ≤ ∑ _k ∈ fouvryG9GridUsed N eps ρ,
        C * N / Real.log (N : ℝ) ^ (A + 4) := Finset.sum_le_sum hlocal
    _ = ((fouvryG9GridUsed N eps ρ).card : ℝ) *
        (C * N / Real.log (N : ℝ) ^ (A + 4)) := by simp
    _ ≤ (D * Real.log (N : ℝ) ^ 3) *
        (C * N / Real.log (N : ℝ) ^ (A + 4)) := by
      apply mul_le_mul_of_nonneg_right (fouvryG9GridCost_card hρ hlog)
      dsimp [C]
      positivity
    _ ≤ _ := fouvryG9GridCost_scalar A hn.le (by linarith) hDC

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
