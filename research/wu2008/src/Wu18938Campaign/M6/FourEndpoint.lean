import Wu18938Campaign.M6.Endpoint
import MathlibNt.Wu2008DoubleSieve.LastPrimeFourPhysicalMap

noncomputable section
open Finset
open Wu2008DoubleSieve
open scoped Classical

namespace Wu18938Campaign.M6

def paperSmallFour (N : ℕ) (e : Bool) : Finset TruncatedFourPhysical.Label :=
  (LastPrimeFour.original N e).filter fun x =>
    (x.1.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)

theorem originalFour_firstPrime_ne_cut {N : ℕ} {e : Bool}
    {x : TruncatedFourPhysical.Label} (hx : x ∈ LastPrimeFour.original N e) :
    (x.1.1 : ℝ) ≠ (N : ℝ) ^ (1 / 10 : ℝ) := by
  obtain ⟨⟨a, b, c, d⟩, n⟩ := x
  have h := LastPrimeFour.original_data hx
  exact prime_ne_tenthRoot h.1 h.2.1

theorem paperSmallFour_eq_strict (N : ℕ) (e : Bool) :
    paperSmallFour N e = (LastPrimeFour.original N e).filter fun x =>
      (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by
  ext x
  simp only [paperSmallFour, mem_filter]
  constructor
  · rintro ⟨hx, hcut⟩
    exact ⟨hx, lt_of_le_of_ne hcut (originalFour_firstPrime_ne_cut hx)⟩
  · rintro ⟨hx, hcut⟩
    exact ⟨hx, hcut.le⟩

theorem paperSmallFour_card_le_profiles (N : ℕ) (e : Bool) :
    (paperSmallFour N e).card ≤
      ((LastPrimeFour.outputProfiles N e).filter fun x =>
        (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ)).card := by
  rw [paperSmallFour_eq_strict]
  apply card_le_card_of_injOn LastPrimeFour.switch
  · intro x hx
    obtain ⟨hx, hcut⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨LastPrimeFour.original_maps hx, hcut⟩
  · exact LastPrimeFour.switch_injective.injOn

end Wu18938Campaign.M6
