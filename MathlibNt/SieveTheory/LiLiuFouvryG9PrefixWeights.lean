import MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixPNT

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual inverse logarithmic weight after eliminating the short box index. -/
def fouvryG9FirstWeight (N : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  1 / (((5/9 : ℝ)*(1-Real.log (n : ℝ)/Real.log (N : ℝ))-δ)*Real.log (N : ℝ))

theorem fouvryG9FirstDenominator_pos {N n : ℕ} {δ : ℝ}
    (hN : 1 < (N : ℝ)) (hδ : δ < 1/4) (hn : 0 < n)
    (hnu : (n : ℝ) < (N : ℝ)^(1/10 : ℝ)) :
    0 < (((5/9 : ℝ)*(1-Real.log (n : ℝ)/Real.log (N : ℝ))-δ)*Real.log (N : ℝ)) := by
  have hLN := Real.log_pos hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hu := Real.log_lt_log hn0 hnu
  rw [Real.log_rpow hN0] at hu
  have huv : Real.log (n : ℝ)/Real.log (N : ℝ) < 1/10 :=
    (div_lt_iff₀ hLN).mpr (by linarith)
  apply mul_pos _ hLN
  linarith

theorem fouvryG9FirstWeight_nonneg {N : ℕ} {ρ δ : ℝ}
    (hN : 1 < (N : ℝ)) (hδ : δ < 1/4) {rs : ℕ × ℕ}
    (hrs : rs ∈ fouvryG9RelaxedPairs N ρ) :
    0 ≤ fouvryG9FirstWeight N δ rs.1 := by
  obtain ⟨_,hp,_,_,hnu,_,_⟩ := mem_filter.mp hrs
  exact (one_div_pos.mpr (fouvryG9FirstDenominator_pos hN hδ hp.pos hnu)).le

/-- Original Qk, including its buffered 2/3 scale: no replacement level or mask. -/
theorem fouvryG9RectanglePrefix_log_weight {N : ℕ} {ρ δ : ℝ}
    (hN : 1 < (N : ℝ)) (hρ : 1 < ρ) (hδ : δ < 1/4)
    {k : ℕ × ℕ × ℕ} {n : ℕ} (hn : n ∈ fouvryG9LongShortLabels N ρ k) :
    1/Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) ≤
      fouvryG9FirstWeight N δ n := by
  obtain ⟨_,hp,_,_,hnu,hnlo,_⟩ := mem_filter.mp hn
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
  have hT0 : 0 < (2/3 : ℝ)*ρ^k.1 := mul_pos (by norm_num) (pow_pos (by linarith) _)
  have hTn : (2/3 : ℝ)*ρ^k.1 ≤ n := by
    nlinarith [pow_pos (by linarith : 0 < ρ) k.1]
  have hlogs := Real.log_le_log hT0 hTn
  have hD := fouvryG9FirstDenominator_pos hN hδ hp.pos hnu
  unfold fouvryG9FirstWeight
  apply one_div_le_one_div_of_le hD
  rw [Real.log_div (Real.rpow_pos_of_pos hN0 _).ne' (Real.rpow_pos_of_pos hT0 _).ne',
    Real.log_rpow hN0,Real.log_rpow hT0]
  have hLN := (Real.log_pos hN).ne'
  have heq : (((5/9 : ℝ)*(1-Real.log (n : ℝ)/Real.log (N : ℝ))-δ)*Real.log (N : ℝ)) =
      (5/9-δ)*Real.log (N : ℝ)-(5/9)*Real.log (n : ℝ) := by
    field_simp
    ring
  rw [heq]
  linarith

/-- Exact prefix logarithm, for the genuinely rho-cubed enlarged product. -/
theorem fouvryG9RectanglePrefix_log_eq {N n s : ℕ} {ρ : ℝ}
    (hN : 1 < (N : ℝ)) (hρ : 0 < ρ) (hn : 0 < n) (hs : 0 < s) :
    Real.log (ρ^3*(N : ℝ)/((n : ℝ)*s)) =
      Real.log (N : ℝ)*(1+3*Real.log ρ/Real.log (N : ℝ)-
        Real.log (n : ℝ)/Real.log (N : ℝ)-Real.log (s : ℝ)/Real.log (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  rw [Real.log_div (mul_pos (pow_pos hρ 3) hN0).ne' (mul_pos hn0 hs0).ne',
    Real.log_mul (pow_pos hρ 3).ne' hN0.ne',Real.log_mul hn0.ne' hs0.ne',Real.log_pow]
  have hLN := (Real.log_pos hN).ne'
  field_simp
  ring

/-- Algebraic assembly into the exact kernel denominator, with no asymptotic loss. -/
theorem fouvryG9RectanglePrefix_kernel_term {N n s : ℕ} {ρ : ℝ}
    (hN : 1 < (N : ℝ)) (hρ : 0 < ρ) (hn : 0 < n) (hs : 0 < s) (δ ζ : ℝ) :
    fouvryG9FirstWeight N δ n *
      ((1+ζ)*(ρ^3*(N : ℝ)/((n : ℝ)*s))/Real.log (ρ^3*(N : ℝ)/((n : ℝ)*s))) =
      ((1+ζ)*ρ^3*(N : ℝ)/Real.log (N : ℝ)^2) *
        (1/((n : ℝ)*s*(1+3*Real.log ρ/Real.log (N : ℝ)-
          Real.log (n : ℝ)/Real.log (N : ℝ)-Real.log (s : ℝ)/Real.log (N : ℝ))*
          ((5/9 : ℝ)*(1-Real.log (n : ℝ)/Real.log (N : ℝ))-δ))) := by
  rw [fouvryG9RectanglePrefix_log_eq hN hρ hn hs]
  unfold fouvryG9FirstWeight
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
