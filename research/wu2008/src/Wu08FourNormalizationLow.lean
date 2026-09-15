import Wu08FourNormalizationTransport

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace Wu08FirstPrimeFour.Normalization

/-- Low-output budget from actual fibres. Zero is in the summation range. -/
theorem low_from_fibres (N : ℕ) (L : Finset Long) (V : Finset ℕ) (z J : ℝ)
    (hz : 0 ≤ z) (hzN : z ≤ 4*N)
    (hf : ∀ r : ℕ, r ≤ 4*N →
      (∑ p ∈ products L ×ˢ V, if output N p.1 p.2=r then alpha L p.1*beta N p.2 else 0) ≤ J) :
    lowRectangle N L V z ≤ J*((⌊z⌋₊ : ℝ)+1) := by
  let W := fun p : ℕ × ℕ => alpha L p.1*beta N p.2
  have hw (p : ℕ × ℕ) : 0 ≤ W p := mul_nonneg (alpha_nonneg _ _) (beta_nonneg _ _)
  have hpoint : ∀ p : ℕ × ℕ,
      W p*(if (output N p.1 p.2 : ℝ)<z then 1 else 0) ≤
        ∑ r ∈ range (⌊z⌋₊+1), if output N p.1 p.2=r then W p else 0 := by
    intro p
    by_cases hp : (output N p.1 p.2 : ℝ)<z
    · have hm : output N p.1 p.2 ∈ range (⌊z⌋₊+1) :=
        mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hz).mpr hp.le))
      simp only [if_pos hp,mul_one]
      rw [sum_eq_single (output N p.1 p.2)]
      · simp
      · intro b _ hb; exact if_neg (Ne.symm hb)
      · exact fun h => (h hm).elim
    · simp only [if_neg hp,mul_zero]
      apply sum_nonneg
      intro r _; split_ifs <;> simp only [hw,le_refl]
  calc
    _ = ∑ p ∈ products L ×ˢ V, W p*(if (output N p.1 p.2 : ℝ)<z then 1 else 0) := by
      rw [sum_product]; rfl
    _ ≤ ∑ p ∈ products L ×ˢ V, ∑ r ∈ range (⌊z⌋₊+1),
        if output N p.1 p.2=r then W p else 0 := sum_le_sum (fun p _ => hpoint p)
    _ = ∑ r ∈ range (⌊z⌋₊+1), ∑ p ∈ products L ×ˢ V,
        if output N p.1 p.2=r then W p else 0 := sum_comm
    _ ≤ ∑ _r ∈ range (⌊z⌋₊+1), J := by
      apply sum_le_sum
      intro r hr
      have hrz := (Nat.le_floor_iff hz).mp (Nat.le_of_lt_succ (mem_range.mp hr))
      exact hf r (by exact_mod_cast hrz.trans hzN)
    _ = _ := by simp; ring

/-- All actual low rectangles are paid, uniformly over z up to sqrt N.
This includes the proper sieve choice z=sqrt(Dinternal). -/
theorem low_total (A : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : Bool, ∀ ξ : ℝ, ∀ z : Key → ℝ,
      (∀ k ∈ occupied N e ξ ρ, 0 ≤ z k ∧ z k ≤ (N : ℝ)^(1/2 : ℝ)) →
      (∑ k ∈ occupied N e ξ ρ, lowRectangle N (longCell N e ξ ρ k) (shortCell ρ k) (z k)) ≤
        (N : ℝ)/log (N : ℝ)^A := by
  obtain ⟨C,hC,hfib⟩ := output_fibre_uniform (κ := (1/4 : ℝ)) (by norm_num)
  let G : ℝ := (1/log ρ+1)^3
  let B : ℝ := 4*C*(5 : ℝ)^(1/4 : ℝ)
  obtain ⟨Ne,he⟩ := eventually_atTop.mp
    (g9Transport_eventually_envelope (G*B) A (μ := (1/4 : ℝ)) (by norm_num))
  refine ⟨Ne,?_⟩
  intro N hN e ξ z hz
  obtain ⟨hn,hl,hpay⟩ := he N hN
  have hn0 : 0 < (N : ℝ) := by linarith
  have hnHalf : (N : ℝ)^(1/2 : ℝ) ≤ N := by
    simpa using (rpow_le_rpow_of_exponent_le hn (show (1/2 : ℝ) ≤ 1 by norm_num))
  have hnHalf1 : 1 ≤ (N : ℝ)^(1/2 : ℝ) := one_le_rpow hn (by norm_num)
  have hlocal : ∀ k ∈ occupied N e ξ ρ,
      lowRectangle N (longCell N e ξ ρ k) (shortCell ρ k) (z k) ≤
        B*(N : ℝ)^(1-(1/4 : ℝ))*log (N : ℝ)^2 := by
    intro k hk
    let J : ℝ := 2*C*(5*(N : ℝ))^(1/4 : ℝ)
    have hJ : 0 ≤ J := by dsimp [J]; positivity
    have hlow := low_from_fibres N (longCell N e ξ ρ k) (shortCell ρ k) (z k) J
      (hz k hk).1 (by have hh := (hz k hk).2.trans hnHalf; linarith)
      (hfib N _ _ (fun t ht => longLabels_positive (mem_filter.mp ht).1))
    have hround : (⌊z k⌋₊ : ℝ)+1 ≤ 2*(N : ℝ)^(1/2 : ℝ) := by
      have hh := (Nat.floor_le (hz k hk).1).trans (hz k hk).2
      linarith
    have heq : J*(2*(N : ℝ)^(1/2 : ℝ)) = B*(N : ℝ)^(1-(1/4 : ℝ)) := by
      dsimp [J,B]
      rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hn0.le]
      have he : (N : ℝ)^(1/4 : ℝ)*(N : ℝ)^(1/2 : ℝ) = (N : ℝ)^(1-(1/4 : ℝ)) := by
        rw [← rpow_add hn0]; norm_num
      calc
        _ = (4*C*(5 : ℝ)^(1/4 : ℝ))*((N : ℝ)^(1/4 : ℝ)*(N : ℝ)^(1/2 : ℝ)) := by ring
        _ = _ := by rw [he]
    calc
      _ ≤ J*((⌊z k⌋₊ : ℝ)+1) := hlow
      _ ≤ J*(2*(N : ℝ)^(1/2 : ℝ)) := mul_le_mul_of_nonneg_left hround hJ
      _ = B*(N : ℝ)^(1-(1/4 : ℝ)) := heq
      _ ≤ _ := le_mul_of_one_le_right (by dsimp [B]; positivity)
        (by nlinarith only [hl,sq_nonneg (log (N : ℝ)-1)])
  calc
    _ ≤ ∑ _k ∈ occupied N e ξ ρ, B*(N : ℝ)^(1-(1/4 : ℝ))*log (N : ℝ)^2 := sum_le_sum hlocal
    _ = ((occupied N e ξ ρ).card : ℝ)*(B*(N : ℝ)^(1-(1/4 : ℝ))*log (N : ℝ)^2) := by simp
    _ ≤ (G*log (N : ℝ)^3)*(B*(N : ℝ)^(1-(1/4 : ℝ))*log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (occupied_card hρ hl) (by dsimp [B]; positivity)
    _ = (G*B)*(N : ℝ)^(1-(1/4 : ℝ))*log (N : ℝ)^5 := by ring
    _ ≤ _ := hpay

#print axioms low_total
end Wu08FirstPrimeFour.Normalization
