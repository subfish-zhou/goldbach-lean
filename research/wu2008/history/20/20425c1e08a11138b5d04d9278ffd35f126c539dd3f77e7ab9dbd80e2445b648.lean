import R2FouvryC2

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace WuPaper.R2Fouvry

theorem original_sieve_cell (A : ℕ) {e ε δ η : ℝ}
    (he : (3/4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : U8Literal.Key,
      OriginalU8.Occupied N e ρ k → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      let D := externalInternalLevel (OriginalU8.level N ρ δ k) η
      let S := externalTags true P D η z
      OriginalU8.sifted N ρ k P ≤
        (∑ t ∈ S, ∑ d ∈ (P.prod id).divisors,
          externalTerm true P D η z t d*OriginalU8.center N ρ k d) +
        (S.card : ℝ)*(physicalScale ρ k/Real.log (physicalScale ρ k)^A) -
        ∑ t ∈ S, OriginalU8.exceptional N ρ δ k P η z t := by
  obtain ⟨N₀,hC2⟩ := original_rosser_error_uniform A he he1 hε hεa hεδ hδ hη hηu
  refine ⟨N₀,?_⟩
  intro N hN ρ hρ hρu k hk P hP hPN z hcut
  obtain ⟨hQ,hD,_,hf⟩ := hC2 N hN ρ hρ hρu k hk true P z
  have hs := OriginalU8.weighted_upper N ρ k P hP hD hη hηu hcut
  have herr : (∑ t ∈ externalTags true P
      (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
      ∑ d ∈ (P.prod id).divisors,
        externalTerm true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z t d*
          OriginalU8.discrepancy N ρ k d) ≤
      ∑ t ∈ externalTags true P
        (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
        ((physicalScale ρ k/Real.log (physicalScale ρ k)^A) -
          OriginalU8.exceptional N ρ δ k P η z t) := by
    apply sum_le_sum
    intro t ht
    rw [OriginalU8.primorial_error_eq N ρ δ k P hP hPN
      (zero_le_one.trans hQ) hD hη hηu t ht]
    exact sub_le_sub_right ((le_abs_self _).trans (hf t ht).2) _
  rw [sum_sub_distrib] at herr
  simp only [sum_const,nsmul_eq_mul] at herr
  dsimp only
  linarith only [hs,herr]

theorem original_physical_prefix (A : ℕ) {e ε δ η : ℝ}
    (he : (3/4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      ((U8Literal.physicalPrefix N e).card : ℝ) ≤
        (∑ k ∈ U8Literal.occupied N e ρ,
          ∑ t ∈ externalTags true P
            (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
            ∑ d ∈ (P.prod id).divisors,
              externalTerm true P
                (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z t d*
                  OriginalU8.center N ρ k d) +
        (∑ k ∈ U8Literal.occupied N e ρ,
          ((externalTags true P
            (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z).card : ℝ)*
              (physicalScale ρ k/Real.log (physicalScale ρ k)^A)) -
        (∑ k ∈ U8Literal.occupied N e ρ,
          ∑ t ∈ externalTags true P
            (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
            OriginalU8.exceptional N ρ δ k P η z t) +
        (U8Literal.outputBad N e P).card := by
  obtain ⟨N₁,hcell⟩ := original_sieve_cell A he he1 hε hεa hεδ hδ hη hηu
  refine ⟨max N₁ 1,?_⟩
  intro N hN ρ hρ hρu P hP hPN z hcut
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_right N₁ 1).trans hN
  have hs := U8Literal.physicalPrefix_le_rectangles_add_outputBad hN1 e hρ P
  have hb := sum_le_sum (s := U8Literal.occupied N e ρ) (fun k hk =>
    hcell N ((le_max_left N₁ 1).trans hN) ρ hρ hρu k
      (U8Literal.Join.occupied_to_original hN1 hρ hk) P hP hPN z hcut)
  simp only [← U8Literal.Join.sifted_eq,sum_sub_distrib,sum_add_distrib] at hb
  exact hs.trans (add_le_add hb le_rfl)

end WuPaper.R2Fouvry

#check @WuPaper.R2Fouvry.original_sieve_cell
#check @WuPaper.R2Fouvry.original_physical_prefix
#print axioms WuPaper.R2Fouvry.original_sieve_cell
#print axioms WuPaper.R2Fouvry.original_physical_prefix
