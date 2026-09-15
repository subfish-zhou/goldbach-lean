import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9TotalError
import MathlibNt.SieveTheory.LiLiuFouvryG9WFBridge

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

universe u

/-- Normalize a finite family by a positive real cardinality budget.
The tag set may be empty, and the budget need not be integral. -/
theorem fouvryG9FamilyCost_envelope {ι : Type u} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) {B H : ℝ} (hB : 0 < B)
    (hH : 0 ≤ H) (hcard : (s.card : ℝ) ≤ B)
    (hf : ∀ t ∈ s, |f t| ≤ H) :
    |(∑ t ∈ s, |f t|) / B| ≤ H := by
  rw [abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hB.le)]
  apply (div_le_iff₀ hB).2
  calc
    _ ≤ ∑ _t ∈ s, H := Finset.sum_le_sum hf
    _ = (s.card : ℝ) * H := by simp
    _ ≤ B * H := mul_le_mul_of_nonneg_right hcard hH
    _ = H * B := mul_comm _ _

/-- A single spare logarithm absorbs any fixed positive real family budget. -/
theorem fouvryG9FamilyCost_absorb (A : ℕ) {B n : ℝ}
    (hn : 0 ≤ n) (hl : 0 < Real.log n) (hB : B ≤ Real.log n) :
    B * (n / Real.log n ^ (A + 1)) ≤ n / Real.log n ^ A := by
  rw [← mul_div_assoc, pow_succ]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hl _) hl) (pow_pos hl _)).2
  have h := mul_le_mul_of_nonneg_right hB (show 0 ≤ n * Real.log n ^ A by positivity)
  nlinarith [h]

/-- Actual G9 rectangle errors for arbitrary finite tagged families.
The common threshold precedes N, every tag set, and every coefficient family.
Only individual original-level signed well-factorability is assumed; no
well-factorability of an aggregate and no error estimate is a hypothesis. -/
theorem fouvryG9RectangleError_family_total {ι : Type u} [DecidableEq ι]
    (j A : ℕ) {B e ε δ ρ : ℝ} (hB : 0 < B)
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ ≤ 1/2) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ S : (ℕ × ℕ × ℕ) → Finset ι,
      ∀ c : (ℕ × ℕ × ℕ) → ι → ℕ → ℝ,
      (∀ k ∈ fouvryG9GridUsed N e ρ, ((S k).card : ℝ) ≤ B) →
      (∀ k ∈ fouvryG9GridUsed N e ρ, ∀ t ∈ S k,
        SignedWellFactorable j
          ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) (c k t)) →
      ∑ k ∈ fouvryG9GridUsed N e ρ,
        ∑ t ∈ S k, |fouvryG9RectangleError N ρ δ k (c k t)| ≤
          (N : ℝ)/Real.log (N : ℝ)^A := by
  have hK : 1 ≤ 2/e := (le_div_iff₀ he).2 (by linarith)
  obtain ⟨N₁,hcells⟩ := fouvryG9RectangleError_uniform j (A+5) he he1 hε hεa hεδ hδ
  obtain ⟨N₂,hcost⟩ := fouvryG9GridCost_total ρ (2/e) (A+1) hρ hK
  refine ⟨max (max N₁ N₂) (Real.exp B), ?_⟩
  intro N hN S c hcard hc
  have hN₁ : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNB : Real.exp B ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hn : 0 < (N : ℝ) := (Real.exp_pos B).trans_le hNB
  have hlogB : B ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hn).2 hNB
  let x : (ℕ × ℕ × ℕ) → ℝ := fun k =>
    4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)
  let F : (ℕ × ℕ × ℕ) → ℝ := fun k =>
    ∑ t ∈ S k, |fouvryG9RectangleError N ρ δ k (c k t)|
  have hF : ∀ k, 0 ≤ F k := fun k => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpaid : ∑ k ∈ fouvryG9GridUsed N e ρ, |F k / B| ≤
      (N : ℝ) / Real.log (N : ℝ) ^ (A+1) := by
    apply hcost N hN₂ e x (fun k => F k / B)
    · intro k hk
      have hne := fouvryG9GridCell_nonempty_iff.mpr hk
      obtain ⟨_,hxlo,hxhi,_,_⟩ := fouvryG9Grid_buffered_geometry he hρ hρu hne
      exact ⟨hxlo,hxhi⟩
    · intro k hk
      have hx1 : 1 ≤ x k := by
        dsimp [x]
        calc
          (1 : ℝ) ≤ 4*1*((2/3 : ℝ)*1) := by norm_num
          _ ≤ 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1) := by
            gcongr <;> exact one_le_pow₀ hρ.le
      have hH : 0 ≤ x k / Real.log (x k) ^ (A+5) :=
        div_nonneg (by linarith) (pow_nonneg (Real.log_nonneg hx1) _)
      have henv := fouvryG9FamilyCost_envelope (S k)
        (fun t => fouvryG9RectangleError N ρ δ k (c k t)) hB hH (hcard k hk)
        (fun t ht => hcells N hN₁ ρ hρ hρu k
          (fouvryG9GridCell_nonempty_iff.mpr hk) (c k t) (hc k hk t ht))
      exact henv
  calc
    _ = B * ∑ k ∈ fouvryG9GridUsed N e ρ, |F k / B| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_of_nonneg (div_nonneg (hF k) hB.le)]
      change F k = B * (F k / B)
      field_simp
    _ ≤ B * ((N : ℝ) / Real.log (N : ℝ) ^ (A+1)) :=
      mul_le_mul_of_nonneg_left hpaid hB.le
    _ ≤ _ := fouvryG9FamilyCost_absorb A hn.le (hB.trans_le hlogB) hlogB

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
