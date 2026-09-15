import MathlibNt.Wu2008DoubleSieve.SignedSieveRemainder

/-!
# The actual common level on Wu convolution boxes

The source's support restriction `d <= V_1*...*V_i` is proved from its
literal tuples, including the unit at depth zero. The natural Rosser
level `floor((Q/V))+1` encodes coefficients supported on `q <= Q/V`.
Its combined-modulus restriction is discharged, not supplied by a record.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem wu_box_support_product_bound {i N d : ℕ} {Δ : ℝ} {V : Fin i → ℝ}
    (hd : d ∈ (Fintype.piFinset (convolutionWuWindows N Δ V)).image
      (fun t => ∏ j, t j)) :
    0 < d ∧ (d : ℝ) ≤ ∏ j, V j := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
  have ht' := Fintype.mem_piFinset.mp ht
  constructor
  · exact prod_pos (fun j _ => (mem_convolutionWuWindows.mp (ht' j)).1.pos)
  · rw [Nat.cast_prod]
    exact prod_le_prod (fun j _ => Nat.cast_nonneg (t j))
      (fun j _ => (mem_convolutionWuWindows.mp (ht' j)).2.2.2.le)

noncomputable def wuCommonRosserLevel {i : ℕ} (N : ℕ) (δ : ℝ) (V : Fin i → ℝ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)⌋₊ + 1

theorem wuCommonRosserLevel_le_combined {i N d : ℕ} {Δ δ : ℝ} {V : Fin i → ℝ}
    (hd : d ∈ (Fintype.piFinset (convolutionWuWindows N Δ V)).image
      (fun t => ∏ j, t j)) :
    wuCommonRosserLevel N δ V ≤ convolutionModulusCutoff N δ / d + 1 := by
  obtain ⟨hd0, hdV⟩ := wu_box_support_product_bound hd
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  unfold wuCommonRosserLevel convolutionModulusCutoff
  rw [← Nat.floor_div_natCast]
  apply Nat.add_le_add_right
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    hd0' hdV

/-- The source common-level restriction now follows solely from the actual
box support. All real cutoffs and the choice of upper/lower sign are free. -/
theorem wu_common_level_family_remainder_le_AP {i N L : ℕ} (Δ δ : ℝ)
    (V : Fin i → ℝ) (upper : Fin L → Bool) (z : Fin L → ℕ → ℝ) :
    |∑ l, convolutionRosserRemainder N (convolutionWuWindows N Δ V)
      (upper l) (fun _ => wuCommonRosserLevel N δ V) (z l)| ≤
        (L : ℝ) * convolutionAPError N (convolutionModulusCutoff N δ)
          (convolutionWuWindows N Δ V) := by
  apply finite_rosser_family_remainder_le_AP
  intro _l d hd
  exact wuCommonRosserLevel_le_combined hd

/-- A genuine uniform signed-remainder producer at the source common
level, with no assumed weight bound, support condition, or AP estimate. -/
theorem wu_common_level_signed_bv (k L : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
        ∀ upper : Fin L → Bool, ∀ z : Fin L → ℕ → ℝ,
        |∑ l, convolutionRosserRemainder N (convolutionWuWindows N Δ V)
          (upper l) (fun _ => wuCommonRosserLevel N δ V) (z l)| ≤
            (L : ℝ) * (C * (N : ℝ) / Real.log N ^ A) := by
  obtain ⟨C, hC, N0, hBV⟩ := wu_signed_rosser_bombieri_vinogradov k L hδ hA
  refine ⟨C, hC, N0, ?_⟩
  intro N hN i hik Δ hlo hhi V hV upper z
  apply hBV N hN i hik Δ hlo hhi V hV upper
  intro _l d hd
  exact wuCommonRosserLevel_le_combined hd

end Wu2008DoubleSieve
