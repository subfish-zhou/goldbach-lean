import MathlibNt.Wu2008DoubleSieve.ConvolutionBV

/-!
# Wu's shrinking prime boxes

Wu (2004), Section 3, (3.1) and (3.13): `η = δ^(k+1)`,
`W_k = N^η`, and `1 + log(N)^(-4) ≤ Δ < 1 + 2 log(N)^(-4)`.
The ordinary-AP estimate below is uniform over these literal convolution
families. The product upper bound and the ordered/squared-prefix restrictions
of `U_k(N)` are not needed for this estimate.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology

/-- Each factor is exactly the coprime-prime indicator on `[V_j/Δ,V_j)`. -/
noncomputable def convolutionWuWindows {i : ℕ} (N : ℕ) (Δ : ℝ)
    (V : Fin i → ℝ) : Fin i → Finset ℕ :=
  fun j => primeWindow N (V j / Δ) (V j)

theorem mem_convolutionWuWindows {i N p : ℕ} {Δ : ℝ} {V : Fin i → ℝ} {j : Fin i} :
    p ∈ convolutionWuWindows N Δ V j ↔
      p.Prime ∧ p.Coprime N ∧ V j / Δ ≤ (p : ℝ) ∧ (p : ℝ) < V j :=
  mem_primeWindow

/-- Uniformly over the permitted `Δ`, shrinking a window loses at most half
of its fixed positive lower-prime exponent. -/
theorem convolutionWuWindows_eventually_lower_cutoff {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ,
      1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
      ∀ V : ℝ, (N : ℝ) ^ η ≤ V →
        (N : ℝ) ^ (η / 2) ≤ V / Δ := by
  have hpow : ∀ᶠ N : ℕ in atTop, (3 : ℝ) ≤ (N : ℝ) ^ (η / 2) :=
    ((tendsto_rpow_atTop (show 0 < η / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 3)
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hpow, hlog, eventually_ge_atTop (1 : ℕ)] with N hpowN hlogN hN
  intro Δ hΔlo hΔhi V hV
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hsmall : Real.log (N : ℝ) ^ (-4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlogN (by norm_num)
  have hΔ0 : 0 < Δ := by
    have := Real.rpow_nonneg hlog0 (-4)
    linarith
  have hΔpow : Δ ≤ (N : ℝ) ^ (η / 2) := by linarith
  apply (le_div_iff₀ hΔ0).mpr
  calc
    (N : ℝ) ^ (η / 2) * Δ ≤ (N : ℝ) ^ (η / 2) * (N : ℝ) ^ (η / 2) :=
      mul_le_mul_of_nonneg_left hΔpow (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ η := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ V := hV

/-- Genuine unconditional ordinary-AP remainder for the Wu convolution boxes.
The same `C,N₀` work for every depth `i ≤ k`, every permitted `Δ`, and every
choice of the `V_j`. In fact the theorem needs neither evenness, `δ < 1/10`,
nor `∏ V_j ≤ N^(1/2-δ)`, so it also covers the source's high-prime blocks. -/
theorem wu_convolution_bombieri_vinogradov (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          convolutionAPError N (convolutionModulusCutoff N δ)
            (convolutionWuWindows N Δ V) ≤ C * (N : ℝ) / Real.log N ^ A := by
  have hη : 0 < δ ^ (k + 1) := pow_pos hδ _
  obtain ⟨C, hC, N₁, hBV⟩ :=
    convolution_bombieri_vinogradov k (show 0 < δ ^ (k + 1) / 2 by positivity) hδ hA
  obtain ⟨N₂, hcut⟩ := eventually_atTop.mp (convolutionWuWindows_eventually_lower_cutoff hη)
  refine ⟨C, hC, max N₁ N₂, ?_⟩
  intro N hN i hik Δ hΔlo hΔhi V hV
  apply hBV N ((le_max_left _ _).trans hN) i hik
  intro j p hp
  obtain ⟨hp, hcop, hlow, _⟩ := mem_convolutionWuWindows.mp hp
  exact ⟨hp, hcop,
    (hcut N ((le_max_right _ _).trans hN) Δ hΔlo hΔhi (V j) (hV j)).trans hlow⟩

end Wu2008DoubleSieve
