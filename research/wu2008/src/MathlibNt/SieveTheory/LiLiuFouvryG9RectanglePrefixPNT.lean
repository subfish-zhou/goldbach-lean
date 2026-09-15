import MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixFinite
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT

noncomputable section
open Finset Filter
open LiLiuPrereqBuchstab
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Identification with the genuine prime-counting function, including the
right endpoint of the prefix. -/
theorem fouvryG9RectanglePrefix_thirds_le_primePi {N : ℕ} {e ρ : ℝ}
    (hρ : 1 < ρ) (n s : ℕ) :
    ((∑ k ∈ fouvryG9GridUsed N e ρ,
      (fouvryG9RectanglePrefixThirds N ρ n s k).card : ℕ) : ℝ) ≤
      primePi (ρ^3*(N : ℝ)/((n : ℝ)*s)) := by
  have h := fouvryG9RectanglePrefix_thirds_sum_le (N := N) (e := e) hρ n s
  have hc : ((range (⌊ρ^3*(N : ℝ)/((n : ℝ)*s)⌋₊+1)).filter Nat.Prime).card =
      Nat.primeCounting ⌊ρ^3*(N : ℝ)/((n : ℝ)*s)⌋₊ := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hc] at h
  unfold primePi
  exact Nat.cast_le.mpr h

/-- One PNT threshold works for every later prefix endpoint. This directly
consumes the proved error envelope, not a PNT hypothesis. -/
theorem fouvryG9RectanglePrefix_uniform_PNT {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ Y : ℝ, 3 ≤ Y ∧ ∀ y ≥ Y, ∀ x ≥ y,
      primePi x ≤ (1+ζ)*(x/Real.log x) := by
  obtain ⟨A, hA⟩ := eventually_atTop.1
    (tendsto_primeErrorEnvelope.eventually (gt_mem_nhds hζ))
  refine ⟨max 3 (max primeErrorStart A), le_max_left _ _, ?_⟩
  intro y hy x hx
  have hstart : primeErrorStart ≤ y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have henv : primeErrorEnvelope y ≤ ζ :=
    (hA y ((le_max_right _ _).trans ((le_max_right _ _).trans hy))).le
  have hx1 : 1 < x := by linarith [primeErrorStart_spec.1]
  have hm : 0 ≤ x/Real.log x := (div_pos (by linarith) (Real.log_pos hx1)).le
  have herr := (le_abs_self (primePi x-x/Real.log x)).trans
    (primePi_error_le hstart hx)
  have hmul := mul_le_mul_of_nonneg_right henv hm
  nlinarith

/-- Genuine finite prefix merging followed by the existing uniform PNT.
The sole size condition is on the prefix endpoint, not on each third box. -/
theorem fouvryG9RectanglePrefix_thirds_PNT {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ Y : ℝ, 3 ≤ Y ∧ ∀ (N : ℕ) (e ρ : ℝ), 1 < ρ → ∀ n s : ℕ,
      Y ≤ ρ^3*(N : ℝ)/((n : ℝ)*s) →
      ((∑ k ∈ fouvryG9GridUsed N e ρ,
        (fouvryG9RectanglePrefixThirds N ρ n s k).card : ℕ) : ℝ) ≤
      (1+ζ)*((ρ^3*(N : ℝ)/((n : ℝ)*s))/
        Real.log (ρ^3*(N : ℝ)/((n : ℝ)*s))) := by
  obtain ⟨Y, hY, h⟩ := fouvryG9RectanglePrefix_uniform_PNT hζ
  refine ⟨Y, hY, ?_⟩
  intro N e ρ hρ n s hx
  exact (fouvryG9RectanglePrefix_thirds_le_primePi (e := e) hρ n s).trans
    (h Y le_rfl _ hx)

#print axioms fouvryG9RectanglePrefix_thirds_le_primePi
#print axioms fouvryG9RectanglePrefix_uniform_PNT
#print axioms fouvryG9RectanglePrefix_thirds_PNT
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
