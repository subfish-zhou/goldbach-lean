import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairPaidLower
import MathlibNt.SieveTheory.LiLiuGoldbachWeightInitial

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open BombieriVinogradov

/-- The original G6 labels, with the smaller selected prime first. -/
noncomputable def goldbachG6Pairs (N : ℕ) (z b : ℝ) : Finset (ℕ × ℕ) :=
  ((goldbachClosedPrimes N z b).sigma (fun s => goldbachClosedPrimes N z (s : ℝ))).image
    (fun a => (a.2, a.1))

/-- The original closed G7 labels; the shared endpoint is not removed. -/
noncomputable def goldbachG7Pairs (N : ℕ) (z b c : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachClosedPrimes N z b) ×ˢ (goldbachClosedPrimes N b c)

theorem mem_goldbachG6Pairs_iff {N : ℕ} {z b : ℝ} {a : ℕ × ℕ} :
    a ∈ goldbachG6Pairs N z b ↔
      a.2 ∈ goldbachClosedPrimes N z b ∧ a.1 ∈ goldbachClosedPrimes N z (a.2 : ℝ) := by
  constructor
  · rintro ha
    obtain ⟨⟨s, r⟩, hsr, heq⟩ := Finset.mem_image.mp ha
    subst a
    exact Finset.mem_sigma.mp hsr
  · rintro ⟨hs, hr⟩
    exact Finset.mem_image.mpr ⟨⟨a.2, a.1⟩, Finset.mem_sigma.mpr ⟨hs, hr⟩, rfl⟩

theorem goldbachG6Pairs_sum_eq (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    (∑ a ∈ goldbachG6Pairs N z b, literalH A N (a.1 * a.2) z) =
      goldbachWeightG6 A N z b := by
  classical
  have hinj : Function.Injective (fun a : (s : ℕ) × ℕ => (a.2, a.1)) := by
    rintro ⟨s, r⟩ ⟨t, q⟩ h
    have hq := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    dsimp at hq ht
    subst q
    subst t
    rfl
  rw [goldbachG6Pairs, Finset.sum_image hinj.injOn,
    goldbachWeightG6, Finset.sum_sigma']

theorem goldbachG7Pairs_sum_eq (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    (∑ a ∈ goldbachG7Pairs N z b c, literalH A N (a.1 * a.2) z) =
      goldbachWeightG7 A N z b c := by
  rw [goldbachG7Pairs, Finset.sum_product, Finset.sum_comm]
  rfl


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
