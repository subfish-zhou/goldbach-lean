import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionBudget
noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace G12FlexibleWF

/-- The complete actual family, including the original factor 400, has arbitrary
logarithmic saving. The cutoff precedes all submothers and all level/cutoff choices. -/
theorem corrections_log_saving (B : ℕ) {η σ : ℝ}
    (hη : 0 < η) (hηu : η < 1/8) (hσ : 0 < σ) :
    ∀ᶠ N : ℕ in atTop, ∀ (ε : ℝ) (A : Finset (ℕ × ℕ)),
      A.image G12RectangleWF.linkedEmbed ⊆ goldbachG12LinkedAtoms N ε → ∀ Z Q : ℝ,
      (N : ℝ)^σ ≤ Q → Q ≤ N → 2 ≤ externalInternalLevel Q η →
      (400 * ∑ t ∈ externalTags true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z,
        let c := externalTerm true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z t
        |G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) c| + |outsidePrimorial N A Z Q c|) ≤
        N/(Real.log N)^B := by
  obtain ⟨N₀,_,hg⟩ := G12RectangleGate.gate_log_saving (B+1 : ℕ)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (800 * Real.exp (8*(η⁻¹)^3)))
  filter_upwards [eventually_ge_atTop (max 4 N₀), hlog,
    G12OutsideBudget.family_log_saving (B+1) hη hηu hσ] with N hN hL ho
  intro ε A hA Z Q hQl hQu hD
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let P := goldbachB10SiftingPrimes N Z
  let D := externalInternalLevel Q η
  let S := externalTags true P D η Z
  let c := fun t => externalTerm true P D η Z t
  have hlevel := externalInternalLevel_level ((Real.rpow_nonneg hn.le σ).trans hQl) hη hηu
  obtain ⟨hcard,hf⟩ := externalTags_card_and_wellFactorable true P Z hD hη hηu
  simp only [hlevel] at hf
  have hgS : (∑ t ∈ S, |G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) (c t)|) ≤
      (S.card : ℝ)*(N/(Real.log N)^(B+1)) := by
    calc
      _ ≤ ∑ _t ∈ S, ((N : ℝ)/(Real.log N)^(B+1)) := by
        apply sum_le_sum
        intro t ht
        have h := hg N (by omega) ε A (Ioc 0 ⌊Q⌋₊) (c t) hA
          (G12RectangleGate.real_interval_subset hQu) (fun d _ => (hf t ht).2.1 d)
        simpa only [Real.rpow_natCast] using h
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hoS := ho ε (A.image G12RectangleWF.linkedEmbed) hA Z Q hQl hQu hD
  simp_rw [outside_linked] at hoS
  have hc := mul_le_mul_of_nonneg_right hcard.le
    (show 0 ≤ (N : ℝ)/(Real.log N)^(B+1) by positivity)
  change (S.card : ℝ)*(N/(Real.log N)^(B+1)) ≤ _ at hc
  change (400 * ∑ t ∈ S, (|G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) (c t)| +
    |outsidePrimorial N A Z Q (c t)|)) ≤ _
  rw [sum_add_distrib]
  calc
    _ ≤ 800 * Real.exp (8*(η⁻¹)^3) * N/(Real.log N)^(B+1) := by
      have ho' : (∑ t ∈ S, |outsidePrimorial N A Z Q (c t)|) ≤
          Real.exp (8*(η⁻¹)^3)*(N/(Real.log N)^(B+1)) := by
        calc
          _ ≤ (S.card : ℝ)*N/(Real.log N)^(B+1) := hoS
          _ = (S.card : ℝ)*(N/(Real.log N)^(B+1)) := by ring
          _ ≤ _ := hc
      have hh := mul_le_mul_of_nonneg_left (add_le_add (hgS.trans hc) ho')
        (show (0 : ℝ) ≤ 400 by norm_num)
      convert hh using 1 <;> first | rfl | ring
    _ ≤ Real.log (N : ℝ)*N/(Real.log N)^(B+1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL hn.le) (by positivity)
    _ = N/(Real.log N)^B := by
      rw [pow_succ]
      field_simp [ne_of_gt hl]

end G12FlexibleWF
