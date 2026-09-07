import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9LevelTransport
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDispersion

noncomputable section
open Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem SignedWellFactorable.factorSupported {j : ℕ} {L : ℝ} {c : ℕ → ℝ}
    (hc : SignedWellFactorable j L c) (hL : 1 ≤ L) : factorSupported L c := by
  obtain ⟨γ,ζ,hγ,hζ,_,_,heq⟩ := hc.2 L 1 hL le_rfl (mul_one L)
  simpa only [← heq,mul_one] using factorConvolution_supported hγ hζ

/-- Enlarging only the summation interval leaves the same supported weight
unchanged. This is not closure of well-factorability under masking. -/
theorem signedError_level_eq_of_support {L L' : ℝ} (hLL' : L ≤ L')
    (U V : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) (hc : factorSupported L c) :
    signedError U V (Ioc 0 ⌊L⌋₊) α β c a =
      signedError U V (Ioc 0 ⌊L'⌋₊) α β c a := by
  unfold signedError reducedModuli
  apply sum_subset (filter_subset_filter _ (Ioc_subset_Ioc_right (Nat.floor_mono hLL')))
  intro q hq hnot
  have hz : c q = 0 := by
    by_contra hn
    obtain ⟨hq0,hqL⟩ := hc q hn
    exact hnot (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hq0,Nat.le_floor hqL⟩,(mem_filter.mp hq).2⟩)
  simp only [hz,zero_mul]

theorem signedError_levels_eq_of_support {L L' : ℝ}
    (U V : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ)
    (hc : factorSupported L c) (hc' : factorSupported L' c) :
    signedError U V (Ioc 0 ⌊L⌋₊) α β c a =
      signedError U V (Ioc 0 ⌊L'⌋₊) α β c a := by
  rcases le_total L L' with h | h
  · exact signedError_level_eq_of_support h U V α β c a hc
  · exact (signedError_level_eq_of_support h U V α β c a hc').symm

/-- The global level is genuinely at least one in the G9 range. -/
theorem g9Scale_global_level_ge_one {N T δ : ℝ} (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hTN : T ≤ N^(1/10 : ℝ)) (hδ : δ ≤ 1/2) :
    1 ≤ N^(5/9-δ)/T^(5/9 : ℝ) := by
  have hden : T^(5/9 : ℝ) ≤ N^(5/9-δ) := by
    calc
      T^(5/9 : ℝ) ≤ (N^(1/10 : ℝ))^(5/9 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hTN (by norm_num)
      _ = N^(1/18 : ℝ) := by rw [← Real.rpow_mul (by linarith : 0 ≤ N)]; norm_num
      _ ≤ N^(5/9-δ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  exact (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < T) _)).2
    (by simpa using hden)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
