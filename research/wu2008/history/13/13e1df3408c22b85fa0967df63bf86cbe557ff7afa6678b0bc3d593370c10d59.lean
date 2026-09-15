import MathlibNt.Wu2008DoubleSieve.Gamma5GainSufficiency

/-!
# Exact complementary count and main-mass assembly

Only the complementary mask receives the classical bound. The improved
cells are recombined through an equality of arithmetic main masses.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

theorem gamma5Gain_approx_le_kernel {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (n : ℕ) (v : ℝ × ℝ) :
    gamma5GainApprox δ n v ≤ gamma5GainKernel δ v := by
  by_cases hex : ∃ j ∈ gamma5GainInner n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j, hj, hv⟩ := hex
    have hr := gamma5Gain_inner_subset hj hv
    have hb := gamma5Gain_triangle_bounds hr.1
    have hsample : gamma5GainV v.1 v.2 ≤ gamma5GainSample n j := by
      have hp : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
      have hS : 0 < gamma5ClassicalS := by norm_num [gamma5ClassicalS]
      dsimp only [gamma5GainSample, gamma5GainV]
      nlinarith [hv.1.1, hv.2.1]
    rw [gamma5Gain_approx_at_cell hj hv, gamma5GainKernel, if_pos hr]
    have heq : gamma5GainH δ (gamma5GainV v.1 v.2) /
        (v.1 * v.2 * (1 - v.1 - v.2)) =
        gamma5GainH δ (gamma5GainV v.1 v.2) * gamma5GainSmooth v := by
      rw [gamma5Gain_smooth_eq hb.1 hb.2.1, gamma5MassKernel, mul_one_div]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (gamma5Gain_H_antitone hδ hδhi hsample)
      (gamma5Gain_smooth_bounds v).1
  · rw [gamma5Gain_approx_zero (by simpa only [not_exists, not_and] using hex)]
    exact (gamma5Gain_kernel_bounds hδ hδhi v).1

theorem gamma5Gain_partition_sum {α : Type*} [Fintype α]
    (L : Finset Gamma5ClassicalLabel) (P : α → Finset Gamma5ClassicalLabel)
    (hd : Pairwise (fun j l => Disjoint (P j) (P l))) (hs : ∀ j, P j ⊆ L)
    (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ L, f x) = (∑ x ∈ L \ univ.biUnion P, f x) + ∑ j, ∑ x ∈ P j, f x := by
  have hsub : univ.biUnion P ⊆ L := by
    intro x hx
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hx
    exact hs j hj
  rw [← sum_biUnion (fun j _ l _ hjl => hd hjl)]
  exact (sum_sdiff hsub).symm

theorem gamma5Gain_count_partition {α : Type*} [Fintype α] {i : ℕ}
    (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Gamma5ClassicalLabel) (P : α → Finset Gamma5ClassicalLabel)
    (hd : Pairwise (fun j l => Disjoint (P j) (P l))) (hs : ∀ j, P j ⊆ L) :
    gamma5ClassicalCount N δ W L =
      gamma5ClassicalCount N δ W (L \ univ.biUnion P) +
        ∑ j, gamma5ClassicalCount N δ W (P j) :=
  gamma5Gain_partition_sum L P hd hs _

theorem gamma5Gain_main_mass_partition {α : Type*} [Fintype α] {i : ℕ}
    (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Gamma5ClassicalLabel) (P : α → Finset Gamma5ClassicalLabel)
    (hd : Pairwise (fun j l => Disjoint (P j) (P l))) (hs : ∀ j, P j ⊆ L) :
    gamma5ClassicalMainMass N δ W L =
      gamma5ClassicalMainMass N δ W (L \ univ.biUnion P) +
        ∑ j, gamma5ClassicalMainMass N δ W (P j) := by
  simp only [gamma5ClassicalMainMass]
  rw [gamma5Gain_partition_sum L P hd hs, mul_add, mul_sum]

theorem gamma5Gain_finite_upper {α : Type*} [Fintype α]
    {C C₀ M M₀ Θ ρ : ℝ} {c m H : α → ℝ}
    (hρ : 0 ≤ ρ) (hc : C = C₀ + ∑ j, c j) (hm : M = M₀ + ∑ j, m j)
    (hm0 : ∀ j, 0 ≤ m j)
    (hC₀ : C₀ ≤ (1 + ρ) ^ 2 * M₀ + ρ * Θ)
    (hcell : ∀ j, c j ≤ (1 - H j + ρ) * m j) :
    C ≤ (1 + ρ) ^ 2 * M - ∑ j, H j * m j + ρ * Θ := by
  have hh : ∀ j, c j ≤ (1 + ρ) ^ 2 * m j - H j * m j := by
    intro j
    have hmul := mul_nonneg (show 0 ≤ ρ + ρ ^ 2 by positivity) (hm0 j)
    nlinarith [hcell j]
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset α)) => hh j)
  rw [sum_sub_distrib, ← mul_sum] at hs
  rw [hc, hm]
  nlinarith

theorem gamma5Gain_weighted_transport {α : Type*} [Fintype α]
    {Θ ρ ζ G : ℝ} {m H J : α → ℝ} (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ)
    (hH : ∀ j, 0 ≤ H j ∧ H j ≤ 1)
    (hm : ∀ j, (J j - ζ) * Θ ≤ m j)
    (hζρ : (Fintype.card α : ℝ) * ζ ≤ ρ)
    (hs : G - ρ ≤ ∑ j, H j * J j) :
    (G - 2 * ρ) * Θ ≤ ∑ j, H j * m j := by
  have hpoint (j : α) : (H j * J j - ζ) * Θ ≤ H j * m j := by
    have h1 := mul_le_mul_of_nonneg_left (hm j) (hH j).1
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hH j).2 hζ) hΘ
    nlinarith
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset α)) => hpoint j)
  simp only [← sum_mul, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  have hcoef : G - 2 * ρ ≤ (∑ j, H j * J j) - (Fintype.card α : ℝ) * ζ := by linarith
  exact (mul_le_mul_of_nonneg_right hcoef hΘ).trans hsum

theorem gamma5Gain_budget {C G ρ ε : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (hε : 16 * (C + 1) * ρ ≤ ε) :
    (1 + ρ) ^ 2 * (C + ρ) - (G - 2 * ρ) + ρ ≤ C - G + ε := by
  have hsq : (1 + ρ) ^ 2 ≤ 1 + 3 * ρ := by nlinarith
  have hfour : (1 + ρ) ^ 2 ≤ 4 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hsq hC
  have h2 := mul_le_mul_of_nonneg_right hfour hρ
  have h3 := mul_nonneg hC hρ
  nlinarith

end Wu2008DoubleSieve
