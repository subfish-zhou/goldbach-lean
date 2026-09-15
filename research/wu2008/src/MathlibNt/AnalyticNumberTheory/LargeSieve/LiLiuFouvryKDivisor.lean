import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaConvolution

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Change only the auxiliary divisor-growth scale, not the original smoothed sum. -/
theorem wMaskedOriginal_abs_le_largeGCD_pair_mass_kscale (j : ℕ)
    {ε Cscale : ℝ} (hε : 0 < ε) (hCscale : 1 ≤ Cscale) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T x : ℝ, 1 ≤ M → 1 ≤ T → 1 ≤ x → M*T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale*x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ (Y : ℝ) (P : WOriginalTuple → Prop),
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C*M*x^ε*∑ p ∈ largeGCDPairs N Y, |β p.1*β p.2| := by
  obtain ⟨D,hD,hbound⟩ := wMaskedOriginal_abs_le_largeGCD_pair_mass j hε
  refine ⟨D*Cscale^ε, by positivity, ?_⟩
  intro M T x hM hT hx hMT N Q hN β c hc a ha hsupport Y P hP
  have hxx : x ≤ Cscale*x := le_mul_of_one_le_left (by linarith) hCscale
  have hb := hbound M T (Cscale*x) hM hT (hx.trans hxx) (hMT.trans hxx)
    N Q hN β c hc a ha hsupport Y P hP
  rw [Real.mul_rpow (by linarith : 0 ≤ Cscale) (by linarith : 0 ≤ x)] at hb
  convert hb using 1
  ring

/-- The original shifted moment is dominated by a larger auxiliary interval.
The original shift and its two-preimage multiplicity are unchanged. -/
theorem highOmega_shifted_tau_sum_le_kscale (r s : ℕ)
    {Cscale x : ℝ} (hC : 1 ≤ Cscale) (hx : 1 ≤ x)
    (a : ℤ) (ha : |(a : ℝ)| ≤ Cscale*x) :
    (∑ t ∈ Ioc 0 ⌊x⌋₊, (fouvryTau r t : ℝ)*fouvryTau s ((t : ℤ)-a).natAbs) ≤
      5*Cscale*x*(1+Real.log (2*Cscale*x))^(r^2+s^2) := by
  have hxx : x ≤ Cscale*x := le_mul_of_one_le_left (by linarith) hC
  calc
    _ ≤ ∑ t ∈ Ioc 0 ⌊Cscale*x⌋₊,
        (fouvryTau r t : ℝ)*fouvryTau s ((t : ℤ)-a).natAbs := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        exact mem_Ioc.mpr ⟨(mem_Ioc.mp ht).1,
          (mem_Ioc.mp ht).2.trans (Nat.floor_mono hxx)⟩
      · intro t _ _; positivity
    _ ≤ 5*(Cscale*x)*(1+Real.log (2*(Cscale*x)))^(r^2+s^2) :=
      highOmega_shifted_tau_sum_le r s (hx.trans hxx) a ha
    _ = _ := by ring_nf

/-- The fixed enlargement costs a constant, not an extra power of the main scale. -/
theorem kscale_log_cost {Cscale x : ℝ} (hC : 1 ≤ Cscale) (hx : 1 ≤ x) (p : ℕ) :
    (1+Real.log (2*Cscale*x))^p ≤
      (1+Real.log Cscale)^p*(1+Real.log (2*x))^p := by
  have hlogC := Real.log_nonneg hC
  have hlogx := Real.log_nonneg (show 1 ≤ 2*x by linarith)
  have he : Real.log (2*Cscale*x) = Real.log Cscale+Real.log (2*x) := by
    rw [show 2*Cscale*x=Cscale*(2*x) by ring,
      Real.log_mul (by linarith : Cscale ≠ 0) (by positivity : 2*x ≠ 0)]
  rw [he, ← mul_pow]
  apply pow_le_pow_left₀ (by linarith)
  nlinarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
