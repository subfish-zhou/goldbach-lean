import OriginalFinitePrefix

noncomputable section
open Finset Filter
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open LiLiuPrereqBuchstab
namespace OriginalU8

def relaxedPairKernel (N : ℕ) (ρ δ : ℝ) : ℝ :=
  ∑ rs ∈ relaxedPairs N ρ,
    1 / ((rs.1 : ℝ)*rs.2*(1+3*Real.log ρ/Real.log (N : ℝ)-
      Real.log (rs.1 : ℝ)/Real.log (N : ℝ)-Real.log (rs.2 : ℝ)/Real.log (N : ℝ))*
      ((5/9 : ℝ)*(1-Real.log (rs.1 : ℝ)/Real.log (N : ℝ))-δ))

theorem original_weight_nonneg {N : ℕ} {ρ δ : ℝ} (hN : 1 < (N : ℝ))
    (hδ : δ < 1/4) {rs : ℕ × ℕ} (hrs : rs ∈ relaxedPairs N ρ) :
    0 ≤ fouvryG9FirstWeight N δ rs.1 := by
  obtain ⟨_,hp,_,_,hnu,_,_⟩ := mem_filter.mp hrs
  exact (one_div_pos.mpr (fouvryG9FirstDenominator_pos hN hδ hp.pos hnu)).le

/-- This uses the actual buffered level and short interval, not modern short labels. -/
theorem original_log_weight {N : ℕ} {e ρ δ : ℝ} (hN : 1 < (N : ℝ))
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hδ : δ < 1/4)
    {k : ℕ × ℕ × ℕ} (hb : 3 ≤ ρ^k.1) (hk : Occupied N e ρ k)
    {n : ℕ} (hn : n ∈ shortLabels N ρ k) :
    1/Real.log (level N ρ δ k) ≤ fouvryG9FirstWeight N δ n := by
  have a := (primeSupport_mem hρ hρu k hb hk n).mp (mem_filter.mp hn).1
  have hp := (mem_filter.mp hn).2.1
  have hN0 : (0 : ℝ) < N := by linarith
  have hT0 : 0 < (2/3 : ℝ)*ρ^k.1 := mul_pos (by norm_num) (pow_pos (by linarith) _)
  have hTn : (2/3 : ℝ)*ρ^k.1 ≤ n := by nlinarith [a.1, pow_pos (by linarith : 0 < ρ) k.1]
  have hlogs := Real.log_le_log hT0 hTn
  have hD := fouvryG9FirstDenominator_pos hN hδ hp.pos a.2.2.2
  unfold fouvryG9FirstWeight
  apply one_div_le_one_div_of_le hD
  unfold level
  rw [Real.log_div (Real.rpow_pos_of_pos hN0 _).ne' (Real.rpow_pos_of_pos hT0 _).ne',
    Real.log_rpow hN0,Real.log_rpow hT0]
  have hLN := (Real.log_pos hN).ne'
  have heq : (((5/9 : ℝ)*(1-Real.log (n : ℝ)/Real.log (N : ℝ))-δ)*Real.log (N : ℝ)) =
      (5/9-δ)*Real.log (N : ℝ)-(5/9)*Real.log (n : ℝ) := by
    field_simp
    ring
  rw [heq]
  linarith

/-- A closed finite two-prime bound for the actual occupied weighted mass. -/
theorem original_mass_le_primePi {N : ℕ} {e ρ δ : ℝ} (hN : 1 < (N : ℝ))
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hδ : δ < 1/4)
    (hb : ∀ k ∈ U8Literal.occupied N e ρ, 3 ≤ ρ^k.1) :
    (∑ k ∈ U8Literal.occupied N e ρ, rectangleMass N ρ k / Real.log (level N ρ δ k)) ≤
      ∑ rs ∈ relaxedPairs N ρ, fouvryG9FirstWeight N δ rs.1 *
        primePi (ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2)) := by
  have hn : 1 ≤ N := by exact_mod_cast hN.le
  have h := original_weighted_prefix hn hρ hρu hb
    (fun k => 1/Real.log (level N ρ δ k)) (fouvryG9FirstWeight N δ)
    (fun _ hrs => original_weight_nonneg hN hδ hrs)
    (fun k hk _ hmem => original_log_weight hN hρ hρu hδ (hb k hk)
      (U8Literal.Join.occupied_to_original hn hρ hk) hmem)
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using h

/-- The existing alpha-free uniform PNT and exact kernel algebra, specialized only
at the pair carrier. No mass inequality is an assumption. -/
theorem original_pair_PNT {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ ρ δ : ℝ, 1 < ρ → δ < 1/4 →
      (∑ rs ∈ relaxedPairs N ρ, fouvryG9FirstWeight N δ rs.1 *
        primePi (ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2))) ≤
        ((1+ζ)*ρ^3*(N : ℝ)/Real.log (N : ℝ)^2)*relaxedPairKernel N ρ δ := by
  obtain ⟨Y,_,hpnt⟩ := fouvryG9RectanglePrefix_uniform_PNT hζ
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le Y 0 (1/3) (by norm_num))
  refine ⟨max 4 Ng,?_⟩
  intro N hN ρ δ hρ hδ
  have hN4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 < (N : ℝ) := by linarith
  have hY : Y ≤ (N : ℝ)^(1/3 : ℝ) := by
    simpa using hg N ((le_max_right _ _).trans hN)
  unfold relaxedPairKernel
  rw [mul_sum]
  apply sum_le_sum
  intro rs hrs
  obtain ⟨_,hn,hs,_,_,hslo,hcurve⟩ := mem_filter.mp hrs
  have hn0 : (0 : ℝ) < rs.1 := by exact_mod_cast hn.pos
  have hs0 : (0 : ℝ) < rs.2 := by exact_mod_cast hs.pos
  have hx : (rs.2 : ℝ) ≤ ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2) := by
    apply (le_div_iff₀ (mul_pos hn0 hs0)).mpr
    nlinarith only [hcurve]
  have hp := hpnt ((N : ℝ)^(1/3 : ℝ)) hY _ (hslo.trans hx)
  calc
    _ ≤ fouvryG9FirstWeight N δ rs.1 *
        ((1+ζ)*(ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2))/
          Real.log (ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2))) := by
      apply mul_le_mul_of_nonneg_left _ (original_weight_nonneg hN1 hδ hrs)
      simpa only [mul_div_assoc] using hp
    _ = _ := fouvryG9RectanglePrefix_kernel_term hN1 (by linarith) hn.pos hs.pos δ ζ

/-- Actual original occupied mass, original alpha, original Q, fixed-e legal.
The next missing analytic step is the full-domain kernel-to-integral limit. -/
theorem original_rectangleMass_le_kernel {e ρ δ ζ : ℝ}
    (he : 0 < e) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hδ : δ < 1/4) (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (∑ k ∈ U8Literal.occupied N e ρ, rectangleMass N ρ k / Real.log (level N ρ δ k)) ≤
        ((1+ζ)*ρ^3*(N : ℝ)/Real.log (N : ℝ)^2)*relaxedPairKernel N ρ δ := by
  obtain ⟨Np,hp⟩ := original_pair_PNT hζ
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (100/1327) (by norm_num))
  refine ⟨max Np (max Ng 4),?_⟩
  intro N hN
  have hNp := (le_max_left _ _).trans hN
  have hr := (le_max_right _ _).trans hN
  have hNg := (le_max_left _ _).trans hr
  have hN4 : (4 : ℝ) ≤ N := (le_max_right _ _).trans hr
  have hN1 : 1 < (N : ℝ) := by linarith
  have hn : 1 ≤ N := by exact_mod_cast hN1.le
  have hsix : 6 ≤ (N : ℝ)^(100/1327 : ℝ) := by simpa using hg N hNg
  have hb : ∀ k ∈ U8Literal.occupied N e ρ, 3 ≤ ρ^k.1 := by
    intro k hk
    have hgeom := geometry he hρ hρu (U8Literal.Join.occupied_to_original hn hρ hk)
    dsimp only at hgeom
    linarith [hgeom.2.2.2.1]
  exact (original_mass_le_primePi hN1 hρ hρu hδ hb).trans (hp N hNp ρ δ hρ hδ)

end OriginalU8
