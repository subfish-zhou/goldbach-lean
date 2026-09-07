import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorFactorDecay

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11_small_inflation {w a : ℝ} (hw : 0 ≤ w) (hw8 : w ≤ 8)
    (ha : 0 < a) (ha1 : a ≤ 1) : (1+a/128)^2*(w+a/8) ≤ w+a := by
  have ha2 : a^2 ≤ a := by nlinarith
  have hsq : (1+a/128)^2 ≤ 1+a/32 := by nlinarith
  calc
    _ ≤ (1+a/32)*(w+a/8) := mul_le_mul_of_nonneg_right hsq (by linarith)
    _ ≤ _ := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hw8)]

/-- All auxiliary errors are absorbed BEFORE the moving grid and its primes.
This is the actual author's weight, not a free coefficient hypothesis. -/
theorem goldbachG11AuthorFactor_paid (C K τ : ℝ) (hC : 0 ≤ C) (hτ : 0 < τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1/4 ∧ ∃ θ₀ : ℝ, 0 < θ₀ ∧ θ₀ < 1/8 ∧
    ∀ δ θ : ℝ, 0 ≤ δ → δ < δ₀ → 0 < θ → θ < θ₀ →
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
    ∀ ε ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k ∈ goldbachG11GridUsed N ε ρ,
    ∀ p ∈ goldbachG11GridShort N ρ k,
      fouvryG9UpperFactor N (goldbachG11MixedLevel N δ ρ k) C K θ*
        fouvryG9BaseEuler N (Real.sqrt N)*goldbachG11EulerCorrection N ≤
      (goldbachG11AuthorWeight (Real.log (p : ℝ)/Real.log (N : ℝ))+τ)*
        (SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) := by
  let a := min τ 1
  have ha : 0 < a := lt_min hτ zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have haτ : a ≤ τ := min_le_left _ _
  let J := 4*Real.exp (-Real.eulerMascheroniConstant)
  have hJ : 0 < J := by dsimp [J]; positivity
  let ζ := a/128
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  let θ₀ := min (1/16 : ℝ) (a/(128*(1+J)*(C+1)))
  have hden : 0 < 128*(1+J)*(C+1) := by positivity
  have hθ₀ : 0 < θ₀ := lt_min (by norm_num) (div_pos ha hden)
  refine ⟨a/512,by positivity,by linarith,θ₀,hθ₀,?_,?_⟩
  · exact (min_le_left _ _).trans_lt (by norm_num)
  intro δ θ hδ hδsmall hθ hθsmall
  have hδu : δ < 1/4 := by linarith
  have hθpay := (le_div_iff₀ hden).mp (hθsmall.le.trans (min_le_right _ _))
  have hJpay : J*C*θ ≤ a/128 := by
    have hh : J*C ≤ (1+J)*(C+1) := by nlinarith
    have hhθ := mul_le_mul_of_nonneg_right hh hθ.le
    nlinarith only [hθpay,hhθ]
  obtain ⟨Mf,hMf,hf⟩ := goldbachG11AuthorFactor_with_errors ζ hζ
  obtain ⟨Mc,_hMc,hc⟩ := goldbachG11EulerCorrection_eventually ζ hζ
  obtain ⟨Me,_hMe,he⟩ := goldbachG11FamilyError_uniform C K θ (a/128) (by positivity)
  obtain ⟨Mg,_hMg,hg⟩ := goldbachG11OrdinaryLevel_gates hδ (by linarith) hθ
  refine ⟨max Mf (max Mc (max Me Mg)),hMf.trans (le_max_left _ _),?_⟩
  intro N hN hEven ε ρ hρ hρu k hk p hp
  obtain ⟨hNf,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hNc,hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hNe,hNg⟩ := max_le_iff.mp hrest
  have hn4 := hMf.trans hNf
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbig := (hg N hNg).1
  have hmain := hf N hNf hEven ε ρ δ θ C K hρ hρu hδ hδu hθ hC hbig k hk p hp
  have hcorr := hc N hNc
  have hcorr0 : 0 ≤ goldbachG11EulerCorrection N := by
    have hh : 0 ≤ (N : ℝ)^(4/53 : ℝ)-2 := by linarith
    unfold goldbachG11EulerCorrection
    positivity
  let r := Real.log (p : ℝ)/Real.log (N : ℝ)
  let w := goldbachG11AuthorWeight r
  have hw : 0 ≤ w := goldbachG11AuthorWeight_nonneg r
  have hw8 : w ≤ 8 := by
    unfold w goldbachG11AuthorWeight
    have hh := min_le_right r (1/10 : ℝ)
    apply (div_le_iff₀ (by linarith : 0 < 5*(1-min r (1/10)))).2
    linarith
  have hlevel := goldbachG11MixedLevel_log_lower hn4 hρ hρu hbig hk hp (δ := δ)
  have hquarter : (1/4 : ℝ)*Real.log (N : ℝ) ≤ Real.log (goldbachG11MixedLevel N δ ρ k) := by
    have hm := min_le_right r (1/10 : ℝ)
    have hh : (1/4 : ℝ) ≤ (5/9 : ℝ)*(1-min r (1/10))-δ := by linarith
    exact (mul_le_mul_of_nonneg_right hh hln.le).trans hlevel
  have herr := he N hNe (goldbachG11MixedLevel N δ ρ k) hquarter
  have hE : 32*δ+J*goldbachG11FamilyErrorFactor (goldbachG11MixedLevel N δ ρ k) C K θ ≤ a/8 := by
    change J*goldbachG11FamilyErrorFactor _ _ _ _ ≤ J*C*θ+a/128 at herr
    linarith
  have hscalar : (1+ζ)*goldbachG11EulerCorrection N*
      (w+32*δ+J*goldbachG11FamilyErrorFactor (goldbachG11MixedLevel N δ ρ k) C K θ) ≤ w+τ := by
    calc
      _ ≤ (1+ζ)*goldbachG11EulerCorrection N*(w+a/8) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hcorr0)
      _ ≤ (1+ζ)^2*(w+a/8) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcorr (by linarith)) (by linarith)
      _ ≤ w+a := goldbachG11_small_inflation hw hw8 ha ha1
      _ ≤ w+τ := add_le_add (le_refl _) haτ
  exact hmain.trans (mul_le_mul_of_nonneg_right hscalar
    (div_nonneg (SingularSeries.liuSingularSeries_pos N).le hln.le))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig