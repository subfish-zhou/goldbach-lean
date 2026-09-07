import MathlibNt.SieveTheory.LiLiuPrereqWFSignedFamily
import Mathlib.Data.Finset.Prod

/-!
# A uniform bound for the actual normalized signed tags

The finite set here is the existing `signedTags`, with one member for each
accepted multiplicity profile, including the empty profile. No factorial
copies are introduced. The estimates do not require any condition on the
supplied prime labelling: numerical acceptance itself bounds every label.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset LiLiuPrereqWFAdmissibility
open scoped Classical

namespace TagCardinality

/-- All words of length at most `R` over the labels less than `J`. -/
def words (J : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | R + 1 => insert [] (((range J) ×ˢ words J R).image fun p => p.1 :: p.2)

theorem mem_words {J R : ℕ} {t : List ℕ}
    (hlen : t.length ≤ R) (hlabel : ∀ j ∈ t, j < J) : t ∈ words J R := by
  induction R generalizing t with
  | zero =>
      have ht : t = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      simp [ht, words]
  | succ R ih =>
      cases t with
      | nil => simp [words]
      | cons j t =>
          apply mem_insert_of_mem
          apply mem_image.mpr
          refine ⟨(j, t), mem_product.mpr ⟨mem_range.mpr (hlabel j (by simp)), ?_⟩, rfl⟩
          exact ih (by simpa using hlen) (fun k hk => hlabel k (by simp [hk]))

theorem card_words_le (J R : ℕ) : (words J R).card ≤ (J + 1) ^ R := by
  induction R with
  | zero => simp [words]
  | succ R ih =>
      calc
        (words J (R + 1)).card ≤
            (((range J) ×ˢ words J R).image fun p => p.1 :: p.2).card + 1 :=
          card_insert_le _ _
        _ ≤ ((range J) ×ˢ words J R).card + 1 :=
          Nat.add_le_add_right (card_image_le) 1
        _ = J * (words J R).card + 1 := by rw [card_product, card_range]
        _ ≤ J * (J + 1) ^ R + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left J ih) 1
        _ ≤ (J + 1) ^ (R + 1) := by
          have hone : 1 ≤ (J + 1) ^ R := Nat.one_le_pow R (J + 1) (by omega)
          rw [pow_succ]
          nlinarith

theorem accepted_prod_lt {upper : Bool} {D ε : ℝ} {t : List ℕ}
    (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (h : SignedTagAccepted upper (geometricLower D ε (ε ^ 9))
      (fun j => geometricLower D ε (ε ^ 9) (j + 1)) D t) :
    (t.map (geometricLower D ε (ε ^ 9))).prod < D := by
  rcases h with ⟨hadm, htest⟩
  split_ifs at htest with hloose
  · exact htest
  · refine lt_of_le_of_lt (List.prod_map_le_prod_map₀ _ _
        (fun j hj => (by norm_num : (0 : ℝ) ≤ 1).trans (hadm.one_le j hj))
        (fun j _ => geometricLower_monotone hD (pow_nonneg hε 9)
          (Nat.le_succ j))) htest.2.1

theorem accepted_length_le {upper : Bool} {D ε : ℝ} {t : List ℕ}
    (hD : 1 < D) (hε : 0 < ε)
    (h : SignedTagAccepted upper (geometricLower D ε (ε ^ 9))
      (fun j => geometricLower D ε (ε ^ 9) (j + 1)) D t) :
    t.length ≤ ⌊(ε⁻¹) ^ 2⌋₊ := by
  have hlo : ∀ j ∈ t, D ^ (ε ^ 2) ≤ geometricLower D ε (ε ^ 9) j := by
    intro j _
    simpa [geometricLower] using
      geometricLower_monotone (ε := ε) hD.le (pow_nonneg hε.le 9) (Nat.zero_le j)
  have hp := List.prod_map_le_prod_map₀ (fun _ : ℕ => D ^ (ε ^ 2))
    (geometricLower D ε (ε ^ 9))
    (fun _ _ => Real.rpow_nonneg (by linarith) _) hlo
  have hpow : D ^ (ε ^ 2 * (t.length : ℝ)) < D ^ (1 : ℝ) := by
    rw [Real.rpow_one, Real.rpow_mul (by linarith : 0 ≤ D), Real.rpow_natCast]
    simpa using hp.trans_lt (accepted_prod_lt hD.le hε.le h)
  have hlen : ε ^ 2 * (t.length : ℝ) < 1 :=
    (Real.rpow_lt_rpow_left_iff hD).mp hpow
  apply (Nat.le_floor_iff (sq_nonneg ε⁻¹)).mpr
  have heq : ε ^ 2 * (ε⁻¹) ^ 2 = 1 := by field_simp
  nlinarith [sq_pos_of_pos hε]

theorem accepted_label_lt {upper : Bool} {D ε : ℝ} {t : List ℕ}
    (hD : 1 < D) (hε : 0 < ε)
    (h : SignedTagAccepted upper (geometricLower D ε (ε ^ 9))
      (fun j => geometricLower D ε (ε ^ 9) (j + 1)) D t)
    {j : ℕ} (hj : j ∈ t) :
    j < ⌊(ε⁻¹) ^ 11⌋₊ + 1 := by
  obtain ⟨i, hi, hij⟩ := List.mem_iff_getElem.mp hj
  have hhead := h.1.head_sq_lt (by omega)
  have hle := h.1.decreasing 0 i (by omega) hi (Nat.zero_le i)
  have hjone := h.1.one_le j hj
  have hheadone := h.1.one_le t[0] (List.getElem_mem (by omega))
  have hjlt : geometricLower D ε (ε ^ 9) j < D := by
    rw [hij] at hle
    nlinarith
  have hexp : ε ^ 2 * (1 + ε ^ 9) ^ j < 1 := by
    apply (Real.rpow_lt_rpow_left_iff hD).mp
    simpa [geometricLower] using hjlt
  have hbern := one_add_mul_le_pow (a := ε ^ 9)
    (by linarith [pow_pos hε 9] : -2 ≤ ε ^ 9) j
  have hmul : (j : ℝ) * ε ^ 11 < 1 := by
    have hm := mul_le_mul_of_nonneg_left hbern (sq_nonneg ε)
    nlinarith [sq_nonneg ε, show ε ^ 2 * ε ^ 9 = ε ^ 11 by ring]
  have heq : ε ^ 11 * (ε⁻¹) ^ 11 = 1 := by field_simp
  have hjbound : (j : ℝ) ≤ (ε⁻¹) ^ 11 := by
    nlinarith [pow_pos hε 11]
  exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr hjbound)

end TagCardinality

/-- An explicit bound independent of the level, prime set, and labelling. -/
theorem signedTags_card_le_uniform (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 1 < D) (hε : 0 < ε) :
    (signedTags upper P D ε label).card ≤
      (⌊(ε⁻¹) ^ 11⌋₊ + 2) ^ ⌊(ε⁻¹) ^ 2⌋₊ := by
  calc
    (signedTags upper P D ε label).card ≤
        (TagCardinality.words (⌊(ε⁻¹) ^ 11⌋₊ + 1) ⌊(ε⁻¹) ^ 2⌋₊).card := by
      apply card_le_card
      intro t ht
      have h := (mem_filter.mp ht).2
      exact TagCardinality.mem_words (TagCardinality.accepted_length_le hD hε h)
        (fun _ hj => TagCardinality.accepted_label_lt hD hε h hj)
    _ ≤ (⌊(ε⁻¹) ^ 11⌋₊ + 2) ^ ⌊(ε⁻¹) ^ 2⌋₊ := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        TagCardinality.card_words_le (⌊(ε⁻¹) ^ 11⌋₊ + 1) ⌊(ε⁻¹) ^ 2⌋₊

#check signedTags_card_le_uniform
#print axioms signedTags_card_le_uniform

end MathlibNt.SieveTheory.LiLiuPrereqWF
