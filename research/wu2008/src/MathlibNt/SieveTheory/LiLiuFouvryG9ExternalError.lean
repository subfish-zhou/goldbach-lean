import MathlibNt.SieveTheory.LiLiuFouvryG9FamilyCost
import MathlibNt.SieveTheory.LiLiuFouvryG9WFFamily

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Total error for the actual normalized external upper family. Both the
well-factorability and the finite-family cardinality are produced internally.
The prime carriers and cutoffs may vary after the common threshold. -/
theorem fouvryG9ExternalError_total (A : ℕ) {e ε δ η ρ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ P : (ℕ × ℕ × ℕ) → Finset ℕ, ∀ z : (ℕ × ℕ × ℕ) → ℝ,
      let D := fun k : ℕ × ℕ × ℕ => externalInternalLevel
        ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) η
      ∑ k ∈ fouvryG9GridUsed N e ρ,
        ∑ t ∈ externalTags true (P k) (D k) η (z k),
          |fouvryG9RectangleError N ρ δ k
            (fun n => externalTerm true (P k) (D k) η (z k) t n)| ≤
              (N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨N₁,hfamily⟩ := g9WF_external_family_at_level
    (hε.le.trans hεδ.le) hδ hη hηu
  obtain ⟨N₂,hcost⟩ := fouvryG9RectangleError_family_total (ι := List ℕ)
    1 A (Real.exp_pos (8*(η⁻¹)^3)) he he1 hε hεa hεδ hδ.le hρ hρu
  obtain ⟨N₃,hpow⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 2 0 (4/53) (by norm_num))
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN P z
  have hN₁ : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₃ : N₃ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have htwo : 2 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using hpow N hN₃
  have hT : ∀ k ∈ fouvryG9GridUsed N e ρ,
      1 ≤ (2/3 : ℝ)*ρ^k.1 ∧ (2/3 : ℝ)*ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ) := by
    intro k hk
    obtain ⟨_,_,_,hlo,hhi⟩ := fouvryG9Grid_buffered_geometry he hρ hρu
      (fouvryG9GridCell_nonempty_iff.mpr hk)
    exact ⟨by linarith, hhi⟩
  apply hcost N hN₂
    (fun k => externalTags true (P k) (externalInternalLevel
      ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) η) η (z k))
    (fun k t n => externalTerm true (P k) (externalInternalLevel
      ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) η) η (z k) t n)
  · intro k hk
    exact (hfamily N _ hN₁ (hT k hk).1 (hT k hk).2 true (P k) (z k)).1.le
  · intro k hk
    exact (hfamily N _ hN₁ (hT k hk).1 (hT k hk).2 true (P k) (z k)).2

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
