import Wu18938Campaign.M6.Endpoint
import U8PhysicalCompatible

noncomputable section
open Finset
open Wu2008DoubleSieve Wu2008DoubleSieve.SeventhEighth
open scoped Classical

namespace Wu18938Campaign.M6

def paperSmallEighth (N : ℕ) : Finset NinthLabel :=
  (physicalT8 N).filter fun x => (x.1.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)

theorem physicalT8_firstPrime_ne_cut {N : ℕ} {x : NinthLabel}
    (hx : x ∈ physicalT8 N) :
    (x.1.1 : ℝ) ≠ (N : ℝ) ^ (1 / 10 : ℝ) := by
  obtain ⟨⟨a, b⟩, r⟩ := x
  have h := lowerPairs_data (mem_physicalT8.mp hx).1
  exact prime_ne_tenthRoot h.1 h.2.2.1

theorem paperSmallEighth_eq (N : ℕ) :
    paperSmallEighth N = U8Literal.physicalSmall N := by
  ext x
  simp only [paperSmallEighth, U8Literal.physicalSmall, mem_filter]
  constructor
  · rintro ⟨hx, hcut⟩
    exact ⟨hx, lt_of_le_of_ne hcut (physicalT8_firstPrime_ne_cut hx)⟩
  · rintro ⟨hx, hcut⟩
    exact ⟨hx, hcut.le⟩

theorem physicalT8_paper_split (N : ℕ) :
    (physicalT8 N).card =
      (paperSmallEighth N).card +
        ((physicalT8 N).filter fun x =>
          (N : ℝ) ^ (1 / 10 : ℝ) < (x.1.1 : ℝ)).card := by
  simpa only [paperSmallEighth, not_le] using
    (card_filter_add_card_filter_not (s := physicalT8 N)
      (fun x => (x.1.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))).symm

theorem paperSmallEighth_le_rectangles {N : ℕ} (hN : 1 ≤ N) (e : ℝ) {ρ : ℝ}
    (hρ : 1 < ρ) (P : Finset ℕ) :
    ((paperSmallEighth N).card : ℝ) ≤
      (∑ k ∈ U8Literal.occupied N e ρ, U8Literal.rectangleSifted N ρ k P) +
        (U8Literal.outputBad N e P).card + (U8Literal.smallPrefix N e).card := by
  rw [paperSmallEighth_eq]
  exact U8Literal.physicalSmall_le_rectangles_add_losses hN e hρ P

end Wu18938Campaign.M6
