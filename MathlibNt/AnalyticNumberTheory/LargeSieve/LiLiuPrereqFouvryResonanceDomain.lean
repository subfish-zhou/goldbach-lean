import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionDomain
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryResonanceCount

/-!
# Excluding the degenerate beta diagonal on the retained IV.3 carrier

Primitivity forces `d₁*n = n₂` to have `n₂ = 1`. The original second
beta coordinate would then be `d ≤ x^η`, contradicting its lower support.
The nonzero differences below are derived from the actual support and mask,
not imposed on the final original carrier.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem iv3_resonance_difference_ne_zero_of_support
    {d d₁ n n₂ : ℕ} {T Y : ℝ} (hc : (d₁ * n).Coprime n₂)
    (hd : (d : ℝ) ≤ Y) (hN₂ : T ≤ (d * n₂ : ℕ)) (hYT : Y < T) :
    (d₁ : ℤ) * n - n₂ ≠ 0 := by
  intro he
  have he' : d₁ * n = n₂ := by exact_mod_cast sub_eq_zero.mp he
  have hn₂ : n₂ = 1 := by
    simpa only [he', Nat.coprime_self] using hc
  rw [hn₂, mul_one] at hN₂
  linarith


/-- The same exclusion in the reconstructed fixed support interface. -/
theorem wKSectionFixedSupport_resonance_difference_ne_zero
    {N : Finset ℕ} {a : ℤ} {x η R S T : ℝ}
    (hNT : ∀ m ∈ N, T ≤ (m : ℝ)) (hT : x ^ η < T)
    {K : WExtractedKey} {r n n₂ s : ℕ}
    (hf : wKSectionFixedCanonical K r n n₂ s)
    (hsup : wKSectionFixedSupport N a x η R S K r n n₂ s) :
    (K.1.2.1 : ℤ) * n - n₂ ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hf
  obtain ⟨_, _, _, hn₂, _, _, _, _, _, hd, _⟩ := hsup
  exact iv3_resonance_difference_ne_zero_of_support hc hd (hNT _ hn₂) hT


theorem iv3_resonance_support_gap
    {x η ε T : ℝ} (hx : 1 < x) (hη : η < ε) (hT : x ^ ε ≤ T) :
    x ^ η < T :=
  (Real.rpow_lt_rpow_of_exponent_lt hx hη).trans_le hT


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
