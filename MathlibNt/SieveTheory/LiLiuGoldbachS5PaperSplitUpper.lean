import MathlibNt.SieveTheory.LiLiuFouvryG9LowFinal
import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachB9SplitIntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachS5FirstPrimeSplit

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal paper coefficient is exactly the two proved analytic coefficients. -/
theorem goldbachB9PaperSplitIntegral_eq_low_high :
    goldbachB9PaperSplitIntegral =
      (36/5 : ℝ)*fouvryG9RelaxedIntegralLow + 8*goldbachB9HighMainIntegral := rfl

/-- The full original S5 sum has the paper's split-integral upper bound.
The strict low and closed high terms partition all original labels exactly. -/
theorem goldbachS5Closed_normalized_upper_paperSplit
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) : ℝ) ≤
        (goldbachB9PaperSplitIntegral+δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨Nl,hNl,hl⟩ := fouvryG9S5Low_integral_upper (δ/2) (by positivity) ε hε
    (by linarith)
  obtain ⟨Nh,_,hh⟩ := goldbachS5HighFirstClosed_normalized_upper_integral
    (δ/2) ε (by positivity) hε hεu
  refine ⟨max Nl Nh,hNl.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hNlN := (le_max_left _ _).trans hN
  have hNhN := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := by have := hNl.trans hNlN; omega
  have hlN := hl N hNlN hEven
  have hhN := hh N hNhN hEven
  have hs := congrArg (fun z : ℤ => (z : ℝ))
    (goldbachS5Closed_actual_split_first N hN2 ε)
  push_cast at hs
  rw [goldbachB9PaperSplitIntegral_eq_low_high]
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
