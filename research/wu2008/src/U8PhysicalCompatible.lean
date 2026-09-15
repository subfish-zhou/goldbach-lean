import U8Geometry
import U8CarrierCompatible

noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SeventhEighth

/-- This is a filter of the original labelled physicalT8, not a replacement carrier. -/
def physicalSmall (N : ℕ) : Finset Label := by
  classical
  exact (physicalT8 N).filter fun x => (x.1.1 : ℝ) < (N : ℝ)^(1/10 : ℝ)

def physicalPrefix (N : ℕ) (e : ℝ) : Finset Label := by
  classical
  exact (physicalSmall N).filter fun x => e*(N : ℝ) < (x.1.1*x.1.2*x.2 : ℕ)
def smallPrefix (N : ℕ) (e : ℝ) : Finset Label := by
  classical
  exact (physicalSmall N).filter fun x => (x.1.1*x.1.2*x.2 : ℕ) ≤ e*(N : ℝ)
def outputBad (N : ℕ) (e : ℝ) (P : Finset ℕ) : Finset Label := by
  classical
  exact (physicalPrefix N e).filter fun x => ¬(output N x.1.1 (x.1.2*x.2)).Coprime (P.prod id)
def siftedPrefix (N : ℕ) (e : ℝ) (P : Finset ℕ) : Finset Label := by
  classical
  exact (physicalPrefix N e).filter fun x => (output N x.1.1 (x.1.2*x.2)).Coprime (P.prod id)
def occupied (N : ℕ) (e ρ : ℝ) : Finset Key := by
  classical
  exact (physicalPrefix N e).image (gridKey ρ)
def cell (N : ℕ) (e ρ : ℝ) (k : Key) : Finset Label := by
  classical
  exact (physicalPrefix N e).filter fun x => gridKey ρ x=k

theorem originalAlpha_eq : originalAlpha = alpha := rfl

theorem physicalSmall_data {N : ℕ} {x : Label} (hx : x ∈ physicalSmall N) :
    x.1.1.Prime ∧ x.1.2.Prime ∧ x.2.Prime ∧
    x.1.1.Coprime N ∧ x.1.2.Coprime N ∧
    (N : ℝ)^originalAlpha ≤ x.1.1 ∧ (x.1.1 : ℝ) < (N : ℝ)^(1/10 : ℝ) ∧
    (N : ℝ)^(1/3 : ℝ) ≤ x.1.2 ∧ x.1.1 < x.1.2 ∧ x.1.2 ≤ x.2 ∧
    x.1.2 < N+1 ∧ x.2 < N+1 ∧ x.1.1*x.1.2*x.2 < N ∧
    (N-x.1.1*x.1.2*x.2).Prime := by
  classical
  obtain ⟨⟨a,b⟩,r⟩ := x
  obtain ⟨hx,hs⟩ := mem_filter.mp hx
  obtain ⟨hp,_,hrN,hr,hbr,hprod,hout⟩ := mem_physicalT8.mp hx
  obtain ⟨ha,hb,hac,hbc,hlo,hblo,hab,_⟩ := lowerPairs_data hp
  have hbN : b < N+1 := by
    have hba : b ≤ a*b := Nat.le_mul_of_pos_left b ha.pos
    have hbar : a*b ≤ a*b*r := Nat.le_mul_of_pos_right (a*b) hr.pos
    omega
  exact ⟨ha,hb,hr,hac,hbc,hlo,hs,hblo,hab,hbr,hbN,hrN,hprod,hout⟩

/-- Every physical cell embeds in a genuinely separated whole-interval rectangle. -/
theorem cell_rectangle {N : ℕ} (hN : 1 ≤ N) {e ρ : ℝ} (hρ : 1 < ρ)
    {k : Key} {x : Label} (hx : x ∈ cell N e ρ k) :
    x.1.1 ∈ shortPrimeSupport N ρ k ∧ (x.1.2,x.2) ∈ longLabels N ρ k := by
  classical
  obtain ⟨hx,hkey⟩ := mem_filter.mp hx
  have hs := (mem_filter.mp hx).1
  obtain ⟨ha,hb,hr,_,hbc,hlo,hhi,hblo,_,hbr,hbN,hrN,_,_⟩ := physicalSmall_data hs
  have ga := gridIndex_bounds hρ (show (1 : ℝ) ≤ x.1.1 by exact_mod_cast ha.one_le)
  have gb := gridIndex_bounds hρ (show (1 : ℝ) ≤ x.1.2 by exact_mod_cast hb.one_le)
  have gr := gridIndex_bounds hρ (show (1 : ℝ) ≤ x.2 by exact_mod_cast hr.one_le)
  have hi := congrArg Prod.fst hkey
  have hj := congrArg (fun k : Key => k.2.1) hkey
  have hl := congrArg (fun k : Key => k.2.2) hkey
  change gridIndex ρ x.1.1 = k.1 at hi
  change gridIndex ρ x.1.2 = k.2.1 at hj
  change gridIndex ρ x.2 = k.2.2 at hl
  rw [hi] at ga
  rw [hj] at gb
  rw [hl] at gr
  refine ⟨(mem_shortPrimeSupport hN hρ k _).mpr ⟨ga.1,hlo,ga.2,hhi⟩,?_⟩
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hbN,mem_range.mpr hrN⟩,
    hb,hr,hbc,hbr,hblo,gb.1,gb.2,gr.1,gr.2⟩

/-- Exact positive partition over keys occupied by the *unfiltered* physicalPrefix. -/
theorem siftedPrefix_partition (N : ℕ) (e ρ : ℝ) (P : Finset ℕ) :
    (∑ k ∈ occupied N e ρ,
      (((siftedPrefix N e P).filter fun x => gridKey ρ x=k).card : ℝ)) =
        ((siftedPrefix N e P).card : ℝ) := by
  classical
  have h := sum_fiberwise_of_maps_to
    (s := siftedPrefix N e P) (t := occupied N e ρ) (g := gridKey ρ)
    (fun x hx => mem_image_of_mem (gridKey ρ) (mem_filter.mp hx).1)
    (fun _ => (1 : ℝ))
  simpa only [sum_const, nsmul_eq_mul, mul_one] using h

/-- Literal domination of all siftable original labels. No count hypothesis. -/
theorem siftedPrefix_le_rectangles {N : ℕ} (hN : 1 ≤ N) (e : ℝ) {ρ : ℝ}
    (hρ : 1 < ρ) (P : Finset ℕ) :
    ((siftedPrefix N e P).card : ℝ) ≤
      ∑ k ∈ occupied N e ρ, rectangleSifted N ρ k P := by
  classical
  rw [← siftedPrefix_partition N e ρ P]
  apply sum_le_sum
  intro k _
  apply labels_le_rectangle
  intro x hx
  obtain ⟨hx,hkey⟩ := mem_filter.mp hx
  obtain ⟨hpre,hcop⟩ := mem_filter.mp hx
  have hc : x ∈ cell N e ρ k := mem_filter.mpr ⟨hpre,hkey⟩
  obtain ⟨hn,hl⟩ := cell_rectangle hN hρ hc
  have hd := physicalSmall_data (mem_filter.mp hpre).1
  exact ⟨hn,hl,hd.1,hd.2.2.2.1,hcop⟩

theorem physicalPrefix_card_split (N : ℕ) (e : ℝ) (P : Finset ℕ) :
    (physicalPrefix N e).card = (siftedPrefix N e P).card + (outputBad N e P).card := by
  classical
  exact (card_filter_add_card_filter_not (s := physicalPrefix N e)
    (fun x => (output N x.1.1 (x.1.2*x.2)).Coprime (P.prod id))).symm

theorem physicalSmall_card_split (N : ℕ) (e : ℝ) :
    (physicalSmall N).card = (physicalPrefix N e).card + (smallPrefix N e).card := by
  classical
  have h := card_filter_add_card_filter_not
    (s := physicalSmall N) (p := fun x : Label => e*(N : ℝ) < (x.1.1*x.1.2*x.2 : ℕ))
  simpa only [not_lt, physicalPrefix, smallPrefix] using h.symm

/-- No coprimality-bad label is silently deleted: the exact output exception remains. -/
theorem physicalPrefix_le_rectangles_add_outputBad {N : ℕ} (hN : 1 ≤ N) (e : ℝ) {ρ : ℝ}
    (hρ : 1 < ρ) (P : Finset ℕ) :
    ((physicalPrefix N e).card : ℝ) ≤
      (∑ k ∈ occupied N e ρ, rectangleSifted N ρ k P) + (outputBad N e P).card := by
  rw [physicalPrefix_card_split, Nat.cast_add]
  have h := siftedPrefix_le_rectangles hN e hρ P
  exact add_le_add h le_rfl

/-- Full original small-first-prime segment, with both unpaid losses explicitly retained. -/
theorem physicalSmall_le_rectangles_add_losses {N : ℕ} (hN : 1 ≤ N) (e : ℝ) {ρ : ℝ}
    (hρ : 1 < ρ) (P : Finset ℕ) :
    ((physicalSmall N).card : ℝ) ≤
      (∑ k ∈ occupied N e ρ, rectangleSifted N ρ k P) +
        (outputBad N e P).card + (smallPrefix N e).card := by
  rw [physicalSmall_card_split N e, Nat.cast_add]
  have h := physicalPrefix_le_rectangles_add_outputBad hN e hρ P
  exact add_le_add h le_rfl

/-- On the original carrier, the integer-absolute-value sieve output is exactly N−product. -/
theorem output_eq_original {N : ℕ} {x : Label} (hx : x ∈ physicalSmall N) :
    output N x.1.1 (x.1.2*x.2) = N-x.1.1*x.1.2*x.2 := by
  have hprod := (physicalSmall_data hx).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm : (x.1.2*x.2)*x.1.1 = x.1.1*x.1.2*x.2 := by ring
  unfold output
  rw [← Nat.cast_mul, hm, ← Nat.cast_sub hprod.le, Int.natAbs_natCast]

/-- A bad output is still prime; this is an explicit small-output sieve boundary, not copN loss. -/
theorem outputBad_prime {N : ℕ} {e : ℝ} {P : Finset ℕ} {x : Label}
    (hx : x ∈ outputBad N e P) : (output N x.1.1 (x.1.2*x.2)).Prime := by
  have hs := (mem_filter.mp (mem_filter.mp hx).1).1
  rw [output_eq_original hs]
  exact (physicalSmall_data hs).2.2.2.2.2.2.2.2.2.2.2.2.2
end U8Literal
