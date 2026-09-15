import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorConvolution

noncomputable section
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Transport the same weight to a larger factorization level. No restriction
or mask is applied to the weight; every split of the new level is covered. -/
theorem SignedWellFactorable.level_mono {k : ℕ} {L L' : ℝ} {c : ℕ → ℝ}
    (hc : SignedWellFactorable k L c) (hL : 1 ≤ L) (hLL' : L ≤ L') :
    SignedWellFactorable k L' c := by
  refine ⟨hc.1, ?_⟩
  intro R S hR hS hRS
  by_cases hLR : L ≤ R
  · obtain ⟨γ, ζ, hγ, hζ, hγb, hζb, heq⟩ := hc.2 L 1 hL le_rfl (mul_one L)
    exact ⟨γ, ζ, (fun n hn => ⟨(hγ n hn).1, (hγ n hn).2.trans hLR⟩),
      (fun n hn => ⟨(hζ n hn).1, (hζ n hn).2.trans hS⟩), hγb, hζb, heq⟩
  · have hR0 : 0 < R := by linarith
    have hdiv : 1 ≤ L / R := (le_div_iff₀ hR0).2 (by linarith)
    have hdivS : L / R ≤ S := (div_le_iff₀ hR0).2 (by nlinarith [hLL'])
    have hprod : R * (L / R) = L := by field_simp
    obtain ⟨γ, ζ, hγ, hζ, hγb, hζb, heq⟩ := hc.2 R (L / R) hR hdiv hprod
    exact ⟨γ, ζ, hγ,
      (fun n hn => ⟨(hζ n hn).1, (hζ n hn).2.trans hdivS⟩), hγb, hζb, heq⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
