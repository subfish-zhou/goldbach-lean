import U8PhysicalCompatible

/-! Exact fixed-pair reduction of the original closed small-product prefix.
No asymptotic estimate is asserted by this finite bridge. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct
open Wu2008DoubleSieve Wu2008DoubleSieve.SeventhEighth

/-- Original pair masks, original alpha, and the necessary closed small-product constraint. -/
def pairs (N : ℕ) (e : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (eighthPairs N).filter fun t =>
    (t.1 : ℝ) < (N : ℝ)^(1/10 : ℝ) ∧ (t.1*t.2^2 : ℕ) ≤ e*(N : ℝ)

/-- A genuine whole integer interval with both original upper boundaries. -/
def interval (N : ℕ) (e : ℝ) (t : ℕ × ℕ) : Finset ℕ := by
  classical
  exact (range (N+1)).filter fun r =>
    t.2 ≤ r ∧ t.1*t.2*r < N ∧ (t.1*t.2*r : ℕ) ≤ e*(N : ℝ)

/-- Both linear forms are prime; the diagonal r=p2 is included. -/
def primePair (N : ℕ) (e : ℝ) (t : ℕ × ℕ) : Finset ℕ := by
  classical
  exact (interval N e t).filter fun r => r.Prime ∧ (N-t.1*t.2*r).Prime

theorem mem_smallPrefix_iff {N : ℕ} {e : ℝ} {x : Label} :
    x ∈ smallPrefix N e ↔ x ∈ physicalSmall N ∧
      (x.1.1*x.1.2*x.2 : ℕ) ≤ e*(N : ℝ) := by
  classical
  exact mem_filter

theorem pair_square_le {N : ℕ} {e : ℝ} {x : Label}
    (hx : x ∈ smallPrefix N e) :
    (x.1.1*x.1.2^2 : ℕ) ≤ e*(N : ℝ) := by
  obtain ⟨hs,hcut⟩ := mem_smallPrefix_iff.mp hx
  have hd := physicalSmall_data hs
  have hbr : x.1.2 ≤ x.2 := hd.2.2.2.2.2.2.2.2.2.1
  have hm : x.1.1*x.1.2^2 ≤ x.1.1*x.1.2*x.2 := by
    simpa only [pow_two, mul_assoc] using Nat.mul_le_mul_left (x.1.1*x.1.2) hbr
  exact (show ((x.1.1*x.1.2^2 : ℕ) : ℝ) ≤ ((x.1.1*x.1.2*x.2 : ℕ) : ℝ) by exact_mod_cast hm).trans hcut

/-- Equality, not an injection discarding copN or the square boundary. -/
theorem smallPrefix_eq_sigma (N : ℕ) (e : ℝ) :
    smallPrefix N e = (pairs N e).sigma (primePair N e) := by
  classical
  ext x
  obtain ⟨⟨a,b⟩,r⟩ := x
  constructor
  · intro hx
    have hsq := pair_square_le hx
    obtain ⟨hs,hcut⟩ := mem_smallPrefix_iff.mp hx
    obtain ⟨ht,ha⟩ := mem_filter.mp hs
    obtain ⟨hp,hav,hrN,hr,hbr,hprod,hout⟩ := mem_physicalT8.mp ht
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨hp,hav⟩,ha,hsq⟩,?_⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hrN,hbr,hprod,hcut⟩,hr,hout⟩
  · intro hx
    obtain ⟨hp,hr⟩ := mem_sigma.mp hx
    obtain ⟨hp,ha,_hsq⟩ := mem_filter.mp hp
    obtain ⟨hp,hav⟩ := mem_filter.mp hp
    obtain ⟨hr,hrp,hout⟩ := mem_filter.mp hr
    obtain ⟨hrN,hbr,hprod,hcut⟩ := mem_filter.mp hr
    exact mem_smallPrefix_iff.mpr ⟨mem_filter.mpr
      ⟨mem_physicalT8.mpr ⟨hp,hav,mem_range.mp hrN,hrp,hbr,hprod,hout⟩,ha⟩,hcut⟩

theorem smallPrefix_card_eq_sum (N : ℕ) (e : ℝ) :
    (smallPrefix N e).card = ∑ t ∈ pairs N e, (primePair N e t).card := by
  rw [smallPrefix_eq_sigma, card_sigma]

theorem smallPrefix_card_real_eq_sum (N : ℕ) (e : ℝ) :
    ((smallPrefix N e).card : ℝ) = ∑ t ∈ pairs N e, ((primePair N e t).card : ℝ) := by
  rw [smallPrefix_card_eq_sum, Nat.cast_sum]

theorem pairs_data {N : ℕ} {e : ℝ} {t : ℕ × ℕ} (ht : t ∈ pairs N e) :
    t.1.Prime ∧ t.2.Prime ∧ (t.1*t.2).Coprime N ∧
    (N : ℝ)^originalAlpha ≤ t.1 ∧ (t.1 : ℝ) < (N : ℝ)^(1/10 : ℝ) ∧
    (N : ℝ)^(1/3 : ℝ) ≤ t.2 ∧ t.1 < t.2 ∧
    (t.1*t.2^2 : ℕ) ≤ e*(N : ℝ) := by
  obtain ⟨ht,ha,hcut⟩ := mem_filter.mp ht
  obtain ⟨ht,_⟩ := mem_filter.mp ht
  obtain ⟨hp,hq,hpc,hqc,hlo,hql,hpq,_⟩ := lowerPairs_data ht
  exact ⟨hp,hq,hpc.mul_left hqc,hlo,ha,hql,hpq,hcut⟩

/-- Exact r cutoff with a positive denominator, retaining the closed boundary. -/
theorem primePair_cutoff {N : ℕ} {e : ℝ} {t : ℕ × ℕ} {r : ℕ}
    (ht : t ∈ pairs N e) (hr : r ∈ primePair N e t) :
    t.2 ≤ r ∧ (r : ℝ) ≤ e*(N : ℝ)/(t.1*t.2 : ℕ) ∧
      (1-e)*(N : ℝ) ≤ (N-t.1*t.2*r : ℕ) := by
  obtain ⟨hi,_,_⟩ := mem_filter.mp hr
  obtain ⟨_,hbr,hprod,hcut⟩ := mem_filter.mp hi
  have hd := pairs_data ht
  have hpos : (0 : ℝ) < (t.1*t.2 : ℕ) := by
    exact_mod_cast Nat.mul_pos hd.1.pos hd.2.1.pos
  refine ⟨hbr, (le_div_iff₀ hpos).mpr ?_, ?_⟩
  · simpa only [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hcut
  · rw [Nat.cast_sub hprod.le]
    nlinarith

end U8Literal.SmallProduct
