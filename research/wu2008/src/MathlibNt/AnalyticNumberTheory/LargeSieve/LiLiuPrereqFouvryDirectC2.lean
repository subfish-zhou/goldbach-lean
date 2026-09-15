import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectTotalCost

/-! Original signed distribution error, with no unproved analytic energy input.
The genuine family-uniform coprime Siegel--Walfisz premise is explicit. -/
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem direct_wellFactorable_signedError_sq_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4*M*T z = x → ε ≤ ν → ν ≤ 1/10 → T z = x^ν →
      ∀ U : Finset ℕ, (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      ∀ α c : ℕ → ℝ, (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      SignedWellFactorable j (x^((5-5*ν)/9-ε)) c →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      signedError U (N z) (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) α (β z) c a ^ 2 ≤
        2*x^2/Real.log x^A := by
  obtain ⟨η,hη,hη1,hηε,hbudget⟩ := c2_direct_common_exponent hε
  obtain ⟨C,hC,hcost⟩ := direct_total_prefix_cost_c2 i k j hε hη hη1 hηε hbudget
  have hpow := direct_power_to_log C hC.le A (show 0 < ε/4 by positivity)
  filter_upwards [hcost, hpow,
    wellFactorable_signedError_sq_le_floor_prefix_c2 (i := i) (j := j) A
      hSW hT hN hβ hε hη] with x hcostx hpowx hreduce
  intro z M ν hM hMT hεν hν hTν U hU α c hα hc a ha hax
  obtain ⟨_hRS,γ,ζ,_hγs,_hζs,hγ,hζ,_hcγ,hred⟩ :=
    hreduce z M ν hM hMT hεν hν hTν U hU α c hα hc
  obtain ⟨b,_hb,K,hK,herr⟩ := hred a ha hax
  have hNT : ∀ n ∈ N z, x^ν ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*x^ν := by
    simpa only [hTν] using hN z
  have heq : x = 4*M*x^ν := by rw [← hTν]; exact hMT.symm
  have hterm := hcostx M ν hM hεν hν heq (N z) hNT U α hU hα
    a ha hax K hK b (β z) γ ζ (hβ z) hγ hζ
  dsimp only at herr hterm
  calc
    _ ≤ _ := herr
    _ ≤ C*x^2*x^(-(ε/4)) + x^2/Real.log x^A := add_le_add hterm le_rfl
    _ ≤ x^2/Real.log x^A + x^2/Real.log x^A := add_le_add hpowx le_rfl
    _ = _ := by ring

/-- C.2 on its original full modulus interval and residue-uniform domain. -/
theorem direct_wellFactorable_signedError_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4*M*T z = x → ε ≤ ν → ν ≤ 1/10 → T z = x^ν →
      ∀ U : Finset ℕ, (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      ∀ α c : ℕ → ℝ, (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      SignedWellFactorable j (x^((5-5*ν)/9-ε)) c →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      |signedError U (N z) (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) α (β z) c a| ≤
        x/Real.log x^A := by
  filter_upwards [direct_wellFactorable_signedError_sq_c2 (i := i) (j := j) (2*A+2)
    hSW hT hN hβ hε, Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (1 : ℝ)] with x hsq hlog hx
  intro z M ν hM hMT hεν hν hTν U hU α c hα hc a ha hax
  have hh := hsq z M ν hM hMT hεν hν hTν U hU α c hα hc a ha hax
  have hl0 : 0 < Real.log x := by linarith
  have hden : (Real.log x^A)^2 * 2 ≤ Real.log x^(2*A+2) := by
    rw [pow_add, show 2*A = A*2 by omega, pow_mul]
    exact mul_le_mul_of_nonneg_left (by nlinarith : (2 : ℝ) ≤ Real.log x^2) (sq_nonneg _)
  have hr : 2*x^2/Real.log x^(2*A+2) ≤ (x/Real.log x^A)^2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hl0 _) (sq_pos_of_pos (pow_pos hl0 A))).2
    nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg x)]
  have hf := hh.trans hr
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hf)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
