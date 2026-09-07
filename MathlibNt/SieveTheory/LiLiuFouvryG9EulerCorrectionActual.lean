import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrection
import MathlibNt.SieveTheory.LiLiuFouvryG9RectangleSieve
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ShortInterval

noncomputable section
open Finset
open scoped Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A nonzero actual long coefficient supplies an actual ordered prime label. -/
theorem g9_longAlpha_ne_zero_labels {N m : ℕ} {ρ : ℝ} {k : ℕ × ℕ × ℕ}
    (hm : fouvryG9LongAlpha N ρ k m ≠ 0) :
    ∃ z ∈ fouvryG9LongLabels N ρ k, z.1 * z.2 = m := by
  have hc : ((fouvryG9LongLabels N ρ k).filter (fun z => z.1 * z.2 = m)).card ≠ 0 := by
    intro hz
    apply hm
    simp [fouvryG9LongAlpha, hz]
  obtain ⟨z, hz⟩ := card_pos.mp (Nat.pos_of_ne_zero hc)
  exact ⟨z, (mem_filter.mp hz).1, (mem_filter.mp hz).2⟩

/-- A genuine large-third witness in the cell controls the entire third box.
This is a geometric premise, not a sieve-main-term premise. The current broad
positive-prefix carrier does not itself supply such a witness. -/
theorem g9_third_box_lower_of_large_witness {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5 / 4) {k : ℕ × ℕ × ℕ}
    (hlarge : ∃ y ∈ fouvryG9GridCell N e ρ k,
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((y.1 / y.2.1 : ℕ) : ℝ)) :
    (N : ℝ) ^ (4 / 53 : ℝ) / 2 ≤ ρ ^ k.2.2 := by
  obtain ⟨y, hy, hyt⟩ := hlarge
  have hlabels := (mem_filter.mp (fouvryG9LongLabels_of_cell hρ hy)).2
  have htu := hlabels.2.2.2.2.2.2.2
  change ((y.1 / y.2.1 : ℕ) : ℝ) < ρ ^ (k.2.2 + 1) at htu
  rw [pow_succ] at htu
  have hp : (N : ℝ) ^ (4 / 53 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hb : 0 ≤ ρ ^ k.2.2 := pow_nonneg (by linarith) _
  have hρ2 : ρ ≤ 2 := by linarith
  have hc := mul_le_mul_of_nonneg_left hρ2 hb
  nlinarith

/-- Actual rectangle estimate, with the unresolved third-box condition exposed.
All other prime support and size conditions are produced from the actual
coefficients and the exact short interval. No copN is imposed on the third prime. -/
theorem g9_actual_weighted_euler_le_of_third_box {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5 / 4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ ^ k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty)
    (h8 : 8 ≤ (N : ℝ) ^ (4 / 53 : ℝ))
    (hthird : (N : ℝ) ^ (4 / 53 : ℝ) / 2 ≤ ρ ^ k.2.2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    let U := fouvryG9LongProducts N ρ k
    let V := fouvryG9RectanglePrimeSupport N ρ k
    let α := fouvryG9LongAlpha N ρ k
    let β := fouvryG9RectangleBeta N
    let L := (N : ℝ) ^ (4 / 53 : ℝ) / 2
    (∑ m ∈ U, ∑ n ∈ V, α m * β n *
      (∏ p ∈ P, (1 - progressionDensity (m * n) p))) ≤
      g9BaseEuler P * (1 + 1 / (L - 2)) ^ 3 *
        (∑ m ∈ U, ∑ n ∈ V, α m * β n) := by
  dsimp only
  apply g9_weighted_euler_three_primes_le P _ _ hP
  · intro m _
    exact fouvryG9LongAlpha_nonneg N ρ k m
  · intro n _
    unfold fouvryG9RectangleBeta primeSWBeta
    split_ifs <;> norm_num
  · linarith
  · intro m _ hm
    obtain ⟨z, hz, he⟩ := g9_longAlpha_ne_zero_labels hm
    obtain ⟨_, hs, ht, _, hsN, _, _, htbox, _⟩ := mem_filter.mp hz
    refine ⟨z.1, z.2, hs, ht, he.symm, ?_, hthird.trans htbox⟩
    have hp : (N : ℝ) ^ (4 / 53 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
    linarith
  · intro n hn hβ
    have hnp : n.Prime := by
      by_contra hp
      simp [fouvryG9RectangleBeta, primeSWBeta, hp] at hβ
    have hnC : n.Coprime N := by
      by_contra hc
      simp [fouvryG9RectangleBeta, hc] at hβ
    have hmem : n ∈ fouvryG9LongShortLabels N ρ k := by
      rw [fouvryG9LongShortLabels_eq_interval hN hρ hρu k hbig hne]
      exact mem_filter.mpr ⟨hn, hnp, hnC⟩
    have hnlo := (mem_filter.mp hmem).2.2.2.1
    exact ⟨hnp, by linarith⟩

/-- The desired actual estimate follows once a genuinely large-third cell
witness is available. This is deliberately not claimed from nonemptiness alone. -/
theorem g9_actual_weighted_euler_le_of_large_witness {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5 / 4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ ^ k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty)
    (h8 : 8 ≤ (N : ℝ) ^ (4 / 53 : ℝ))
    (hlarge : ∃ y ∈ fouvryG9GridCell N e ρ k,
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((y.1 / y.2.1 : ℕ) : ℝ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    let U := fouvryG9LongProducts N ρ k
    let V := fouvryG9RectanglePrimeSupport N ρ k
    let α := fouvryG9LongAlpha N ρ k
    let β := fouvryG9RectangleBeta N
    let L := (N : ℝ) ^ (4 / 53 : ℝ) / 2
    (∑ m ∈ U, ∑ n ∈ V, α m * β n *
      (∏ p ∈ P, (1 - progressionDensity (m * n) p))) ≤
      g9BaseEuler P * (1 + 1 / (L - 2)) ^ 3 *
        (∑ m ∈ U, ∑ n ∈ V, α m * β n) := by
  exact g9_actual_weighted_euler_le_of_third_box hN hρ hρu k hbig hne h8
    (g9_third_box_lower_of_large_witness hN hρ hρu hlarge) P hP

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
