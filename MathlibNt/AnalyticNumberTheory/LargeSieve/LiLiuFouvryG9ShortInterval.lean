import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9LongRectangle
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9IntervalEndpoints

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The endpoints of an occupied cell have a genuine interval between them. -/
theorem fouvryG9Grid_short_endpoints {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ)
    {k : ℕ × ℕ × ℕ} (hne : (fouvryG9GridCell N e ρ k).Nonempty) :
    max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ)) ≤
      min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ)) := by
  obtain ⟨y,hy⟩ := hne
  have hn := fouvryG9LongShortLabels_of_cell hρ hy
  obtain ⟨_,_,_,ha,hb,hl,hu⟩ := mem_filter.mp hn
  exact (max_le hl ha).trans (le_min hu.le hb.le)

/-- The actual short-coordinate geometry, with exact integer endpoint encoding. -/
def fouvryG9GridPrimeInterval {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ)
    (hρu : ρ ≤ 5/4) (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty) : PrimeC2Interval :=
  g9PrimeHalfOpenInterval (ρ^k.1) (max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ)))
    (min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ))) hbig (le_max_left _ _)
    (fouvryG9Grid_short_endpoints hρ hne) (by
      apply (min_le_left _ _).trans
      rw [pow_succ]
      nlinarith [pow_pos (by linarith : 0 < ρ) k.1])

/-- The finite short-label set equals the interval filtered by the two literal
arithmetic conditions. There is no condition on the third prime. -/
theorem fouvryG9LongShortLabels_eq_interval {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty) :
    let z := fouvryG9GridPrimeInterval hρ hρu k hbig hne
    fouvryG9LongShortLabels N ρ k =
      (primeSWInterval z.lower z.upper).filter (fun n => n.Prime ∧ n.Coprime N) := by
  ext n
  have hmem := mem_g9PrimeHalfOpenInterval (ρ^k.1)
    (max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ)))
    (min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ))) hbig (le_max_left _ _)
    (fouvryG9Grid_short_endpoints hρ hne)
    (show min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ)) ≤ (4/3 : ℝ)*ρ^k.1 by
      apply (min_le_left _ _).trans
      rw [pow_succ]
      nlinarith [pow_pos (by linarith : 0 < ρ) k.1]) n
  dsimp only at hmem
  change n ∈ (range (N+1)).filter _ ↔ n ∈ (primeSWInterval _ _).filter _
  rw [mem_filter, mem_filter]
  unfold fouvryG9GridPrimeInterval
  rw [hmem, max_le_iff, lt_min_iff]
  constructor
  · rintro ⟨_,hp,hc,ha,hb,hl,hu⟩
    exact ⟨⟨⟨hl,ha⟩,⟨hu,hb⟩⟩,hp,hc⟩
  · rintro ⟨⟨⟨hl,ha⟩,⟨hu,hb⟩⟩,hp,hc⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpow : (N : ℝ)^(1/10 : ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
        (show (1/10 : ℝ) ≤ 1 by norm_num)
    have hnN : n < N := by exact_mod_cast hb.trans_le hpow
    exact ⟨mem_range.mpr (by omega),hp,hc,ha,hb,hl,hu⟩

/-- An arbitrary signed finite kernel is transferred exactly to the existing
prime/copN coefficient, not merely bounded by it. -/
theorem fouvryG9LongShortLabels_sum_interval {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty) (F : ℕ → ℝ) :
    let z := fouvryG9GridPrimeInterval hρ hρu k hbig hne
    (∑ n ∈ fouvryG9LongShortLabels N ρ k, F n) =
      ∑ n ∈ primeSWInterval z.lower z.upper,
        (if n.Coprime N then primeSWBeta n else 0) * F n := by
  dsimp only
  rw [fouvryG9LongShortLabels_eq_interval hN hρ hρu k hbig hne, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime <;> by_cases hc : n.Coprime N <;>
    simp [primeSWBeta, hp, hc]

/-- Positive enlargement now lands in the literal prime interval coefficient
accepted by expanded C2, with the actual long multiplicity unchanged. -/
theorem fouvryG9Long_cell_le_prime_rectangle {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty)
    (F : ℕ → ℕ → ℝ) (hF : ∀ n m, 0 ≤ F n m) :
    let z := fouvryG9GridPrimeInterval hρ hρu k hbig hne
    (∑ y ∈ fouvryG9GridCell N e ρ k, F y.2.2 y.1) ≤
      ∑ m ∈ fouvryG9LongProducts N ρ k, ∑ n ∈ primeSWInterval z.lower z.upper,
        fouvryG9LongAlpha N ρ k m *
          (if n.Coprime N then primeSWBeta n else 0) * F n m := by
  have h := fouvryG9Long_cell_le_weighted_rectangle (N := N) (eps := e) hρ k F hF
  rw [fouvryG9LongShortLabels_sum_interval hN hρ hρu k hbig hne] at h
  simp_rw [mul_sum] at h
  rw [sum_comm] at h
  refine h.trans_eq (sum_congr rfl (fun m _ => sum_congr rfl (fun n _ => ?_)))
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
