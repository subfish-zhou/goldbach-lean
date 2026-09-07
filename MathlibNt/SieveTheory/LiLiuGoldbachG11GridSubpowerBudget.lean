import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridCost
import MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment

open Finset Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The full occupied G11 grid, not just its low subfamily. -/
theorem goldbachG11GridCost_card {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hlog : 1 ≤ Real.log (N : ℝ)) :
    ((goldbachG11GridUsed N ε ρ).card : ℝ) ≤
      (1/Real.log ρ+1)^3*Real.log (N : ℝ)^3 := by
  have hlogρ := Real.log_pos hρ
  have hfloor : (fouvryG9GridIndex ρ N : ℝ) ≤ Real.log N/Real.log ρ :=
    Nat.floor_le (by positivity)
  have hb : (fouvryG9GridIndex ρ N : ℝ)+1 ≤ (1/Real.log ρ+1)*Real.log N := by
    have he : (1/Real.log ρ+1)*Real.log N = Real.log N/Real.log ρ+Real.log N := by ring
    rw [he]
    linarith
  have hcard : ((goldbachG11GridUsed N ε ρ).card : ℝ) ≤
      ((fouvryG9GridIndex ρ N : ℝ)+1)^2 := by exact_mod_cast goldbachG11GridUsed_card (N := N) (ε := ε) hρ
  have hbone : 1 ≤ (fouvryG9GridIndex ρ N : ℝ)+1 := by
    have hh : (0 : ℝ) ≤ fouvryG9GridIndex ρ N := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ ((fouvryG9GridIndex ρ N : ℝ)+1)^2 := hcard
    _ ≤ ((fouvryG9GridIndex ρ N : ℝ)+1)^3 := pow_le_pow_right₀ hbone (by omega)
    _ ≤ ((1/Real.log ρ+1)*Real.log N)^3 := pow_le_pow_left₀ (by positivity) hb 3
    _ = _ := by rw [mul_pow]

/-- Reuse the existing fixed-power/log payment on the literal two-dimensional
G11 grid. This generic finite envelope is instantiated with actual errors. -/
theorem goldbachG11Grid_subpower_sum (A : ℕ) {B μ ρ : ℝ}
    (hB : 0 ≤ B) (hμ : 0 < μ) (hρ : 1 < ρ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      1 ≤ (N : ℝ) ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ (ε : ℝ) (E : (ℕ × ℕ) → ℝ),
      (∀ k ∈ goldbachG11GridUsed N ε ρ,
        E k ≤ B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2) →
      (∑ k ∈ goldbachG11GridUsed N ε ρ, E k) ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
  let G : ℝ := (1/Real.log ρ+1)^3
  obtain ⟨M,hM⟩ := eventually_atTop.mp (g9Transport_eventually_envelope (G*B) A hμ)
  refine ⟨M,?_⟩
  intro N hN
  obtain ⟨hn,hl,hpay⟩ := hM N hN
  refine ⟨hn,hl,?_⟩
  intro ε E hE
  calc
    _ ≤ ∑ _k ∈ goldbachG11GridUsed N ε ρ, B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2 := sum_le_sum hE
    _ = ((goldbachG11GridUsed N ε ρ).card : ℝ)*(B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2) := by simp
    _ ≤ (G*Real.log (N : ℝ)^3)*(B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (goldbachG11GridCost_card hρ hl) (by positivity)
    _ = (G*B)*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^5 := by ring
    _ ≤ _ := hpay

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig