import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4QuadraticSmallValueRealZero
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaExceptionalUniqueness

noncomputable section
open Set Complex
namespace AnalyticNumberTheory.LargeSieve

/-- Classical ineffective dichotomy. The zero witness need not have minimal
conductor. The width pays a Q³ error after an eighth-power cutoff (24δ≤η/2).
This is not yet the raw lower bound: the real-zero branch remains explicit. -/
theorem fourFactor_siegel_noZero_or_witness (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/8 ∧ 48*δ ≤ η ∧
      ((∃ ξ : PrimitiveQuadraticDatum, ∃ β : ℝ,
          β ∈ Ioo (1-δ) 1 ∧
          (let : NeZero ξ.modulus := ⟨ξ.modulus_ne⟩
           ξ.character.LFunction (β : ℂ) = 0)) ∨
       (∃ c : ℝ, 0 < c ∧
         ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
           χ.IsPrimitive → χ^2 = 1 → χ ≠ 1 →
           c*(q:ℝ)^(-η) ≤ (χ.LFunction 1).re)) := by
  classical
  obtain ⟨ε₀, hε₀, _hε₀4, hsmall⟩ :=
    Bombieri1965Theorem4.exists_uniform_small_value_real_zero_neighborhood
  -- One width satisfies both the small-value criterion and the later cutoff budget.
  let δ := min ε₀ (min (1/8) (η/48))
  have hδ : 0 < δ := lt_min hε₀ (lt_min (by norm_num) (by positivity))
  have hδε : δ ≤ ε₀ := min_le_left _ _
  have hδ8 : δ ≤ 1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδη : 48*δ ≤ η := by
    have hδ48 : δ ≤ η/48 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hδ48]
  refine ⟨δ, hδ, hδ8, hδη, ?_⟩
  by_cases hwitness : ∃ ξ : PrimitiveQuadraticDatum, ∃ β : ℝ,
      β ∈ Ioo (1-δ) 1 ∧
      (let : NeZero ξ.modulus := ⟨ξ.modulus_ne⟩
       ξ.character.LFunction (β : ℂ) = 0)
  · exact Or.inl hwitness
  · apply Or.inr
    -- Without a zero witness, the contrapositive gives a uniform positive threshold.
    let c := δ / (4*(648:ℝ)^(4*δ))
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, ?_⟩
    intro q _ χ hprim hquad hχ
    have hq0 : (0:ℝ) < q := by exact_mod_cast (NeZero.pos q)
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hthreshold : δ/(4*(648*(q:ℝ))^(4*δ)) < (χ.LFunction 1).re := by
      by_contra hn
      obtain ⟨β, hβ, hz⟩ := hsmall δ hδ hδε q χ hprim hχ hquad (le_of_not_gt hn)
      exact hwitness ⟨⟨q, NeZero.ne q, χ, hprim, hquad, hχ⟩, β, hβ, hz⟩
    calc
      c*(q:ℝ)^(-η) ≤ c*(q:ℝ)^(-(4*δ)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith only [hδ, hδη])
      _ = δ/(4*(648*(q:ℝ))^(4*δ)) := by
        dsimp [c]
        rw [Real.rpow_neg hq0.le, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 648) hq0.le]
        ring
      _ ≤ (χ.LFunction 1).re := hthreshold.le

end AnalyticNumberTheory.LargeSieve
