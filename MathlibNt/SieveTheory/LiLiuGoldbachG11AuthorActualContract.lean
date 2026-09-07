import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorActualProducer

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact actual-count input expected by the existing final assembly. The
small-epsilon window is furnished here, not assumed by a downstream caller. -/
theorem goldbachWeightG11_author_actual_small_epsilon :
    ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
          ((10191/100000 : ℝ)+δ)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  intro δ hδ
  refine ⟨1,by norm_num,?_⟩
  intro ε hε hεu
  obtain ⟨N₀,_hN₀,hb⟩ := goldbachWeightG11_le_authorScalar_direct δ ε hδ hε hεu.le
  exact ⟨N₀,hb⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig