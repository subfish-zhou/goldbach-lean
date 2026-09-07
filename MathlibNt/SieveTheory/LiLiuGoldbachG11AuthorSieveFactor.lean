import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorLevel

open Finset
open scoped BigOperators Classical
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11FamilyErrorFactor (Q C K θ : ℝ) : ℝ :=
  C*(θ+(θ^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))

theorem goldbachG11MixedLevel_positive {N : ℕ} {δ ρ : ℝ}
    (hN : 0 < N) (hρ : 0 < ρ) (k : ℕ × ℕ) : 0 < goldbachG11MixedLevel N δ ρ k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold goldbachG11MixedLevel goldbachG11GridLowLevel goldbachG11OrdinaryLevel
  split_ifs <;> positivity

theorem goldbachG11MixedLevel_le_originalN {N : ℕ} {ε ρ δ : ℝ}
    (hN : 4 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ)) (hδ : 0 ≤ δ)
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ) :
    goldbachG11MixedLevel N δ ρ k ≤ N := by
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hn0 : (0 : ℝ) ≤ N := by linarith
  unfold goldbachG11MixedLevel
  split_ifs
  · have hT : (1 : ℝ) ≤ (2/3 : ℝ)*ρ^k.1 := by
      have hh := goldbachG11Grid_short_scale_lower hρ hρu hk
      linarith
    have hpow : (1 : ℝ) ≤ ((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ) := Real.one_le_rpow hT (by norm_num)
    unfold goldbachG11GridLowLevel
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpow)).2
    have hh : (N : ℝ)^(5/9-δ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : (5/9 : ℝ)-δ ≤ 1)
    exact hh.trans (le_mul_of_one_le_right hn0 hpow)
  · unfold goldbachG11OrdinaryLevel
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : (1/2 : ℝ)-δ ≤ 1)

/-- Exact cancellation of the Euler--Mascheroni normalization, retaining the
actual external-family error rather than discarding it. -/
theorem goldbachG11UpperFactor_normalization {N : ℕ} {Q C K θ : ℝ}
    (hN : 4 ≤ N) (hQ : 0 < Q) (hlogQ : 0 < Real.log Q) (hQN : Q ≤ N) :
    4*Real.exp (-Real.eulerMascheroniConstant)*fouvryG9UpperFactor N Q C K θ =
      4*Real.log (N : ℝ)/Real.log Q+4*Real.exp (-Real.eulerMascheroniConstant)*
        goldbachG11FamilyErrorFactor Q C K θ := by
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hcoord : Real.log Q/Real.log (Real.sqrt N) ≤ 3 := by
    rw [Real.log_sqrt hn.le]
    apply (div_le_iff₀ (by positivity : 0 < Real.log (N : ℝ)/2)).2
    have hh := Real.log_le_log hQ hQN
    linarith
  unfold fouvryG9UpperFactor goldbachG11FamilyErrorFactor
  rw [jr1965F_eq_of_le_three hcoord,Real.log_sqrt hn.le,Real.exp_neg]
  field_simp

/-- Finite normalized author-weight bound, including every sieve and Euler
correction. Subsequent small-parameter choices may absorb them, not erase them. -/
theorem goldbachG11AuthorFactor_with_errors (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
    ∀ ε ρ δ θ C K : ℝ, 1 < ρ → ρ ≤ 5/4 → 0 ≤ δ → δ < 1/4 → 0 < θ → 0 ≤ C →
    4 ≤ (N : ℝ)^(4/53 : ℝ) → ∀ k ∈ goldbachG11GridUsed N ε ρ,
    ∀ p ∈ goldbachG11GridShort N ρ k,
      fouvryG9UpperFactor N (goldbachG11MixedLevel N δ ρ k) C K θ*
        fouvryG9BaseEuler N (Real.sqrt N)*goldbachG11EulerCorrection N ≤
      (1+ζ)*goldbachG11EulerCorrection N*
        (goldbachG11AuthorWeight (Real.log (p : ℝ)/Real.log (N : ℝ))+32*δ+
          4*Real.exp (-Real.eulerMascheroniConstant)*goldbachG11FamilyErrorFactor
            (goldbachG11MixedLevel N δ ρ k) C K θ)*
        (SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) := by
  obtain ⟨M,hM⟩ := fouvryG9BaseEuler_sqrt_upper ζ hζ
  refine ⟨max 4 ⌈M⌉₊,le_max_left _ _,?_⟩
  intro N hN hEven ε ρ δ θ C K hρ hρu hδ hδu hθ hC hbig k hk p hp
  obtain ⟨hn4,hNm⟩ := max_le_iff.mp hN
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Q := goldbachG11MixedLevel N δ ρ k
  have hq0 : 0 < Q := goldbachG11MixedLevel_positive (by omega) (by linarith) k
  have hqN : Q ≤ N := goldbachG11MixedLevel_le_originalN hn4 hρ hρu hbig hδ hk
  have hlo := goldbachG11MixedLevel_log_lower hn4 hρ hρu hbig hk hp (δ := δ)
  have hmin := min_le_right (Real.log (p : ℝ)/Real.log (N : ℝ)) (1/10 : ℝ)
  have hb : 0 < (5/9 : ℝ)*(1-min (Real.log (p : ℝ)/Real.log (N : ℝ)) (1/10))-δ := by linarith
  have hlogQ : 0 < Real.log Q := (mul_pos hb hln).trans_le hlo
  have he := goldbachG11UpperFactor_normalization (C := C) (K := K) (θ := θ) hn4 hq0 hlogQ hqN
  have herr : 0 ≤ goldbachG11FamilyErrorFactor Q C K θ := by
    unfold goldbachG11FamilyErrorFactor
    positivity
  have hf : 0 ≤ fouvryG9UpperFactor N Q C K θ := by
    have hh : 0 ≤ 4*Real.exp (-Real.eulerMascheroniConstant)*fouvryG9UpperFactor N Q C K θ := by
      rw [he]
      positivity
    exact nonneg_of_mul_nonneg_right hh (by positivity)
  have hcorr : 0 ≤ goldbachG11EulerCorrection N := by
    have hh : 0 ≤ (N : ℝ)^(4/53 : ℝ)-2 := by linarith
    unfold goldbachG11EulerCorrection
    positivity
  have heuler := (le_div_iff₀ hln).2 (hM N ((Nat.le_ceil M).trans (by exact_mod_cast hNm)) hEven)
  have hweight := goldbachG11MixedLevel_author_weight hn4 hρ hρu hbig hδ hδu hk hp
  calc
    _ ≤ fouvryG9UpperFactor N Q C K θ*
        (4*Real.exp (-Real.eulerMascheroniConstant)*(1+ζ)*SingularSeries.liuSingularSeries N/Real.log (N : ℝ))*
        goldbachG11EulerCorrection N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heuler hf) hcorr
    _ = (1+ζ)*goldbachG11EulerCorrection N*
        (4*Real.exp (-Real.eulerMascheroniConstant)*fouvryG9UpperFactor N Q C K θ)*
        (SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) := by ring
    _ = (1+ζ)*goldbachG11EulerCorrection N*
        (4*Real.log (N : ℝ)/Real.log Q+4*Real.exp (-Real.eulerMascheroniConstant)*goldbachG11FamilyErrorFactor Q C K θ)*
        (SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hweight (le_refl _)) (mul_nonneg (by linarith) hcorr))
      (div_nonneg (SingularSeries.liuSingularSeries_pos N).le hln.le)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig