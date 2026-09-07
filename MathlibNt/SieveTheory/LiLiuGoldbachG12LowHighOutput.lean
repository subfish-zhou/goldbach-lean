import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMass

set_option maxHeartbeats 2000000

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12LowHighOutput

/-- The physical original carrier, with the original coprimality and strict
product endpoint. No output primality is assumed in this carrier. -/
def globalLinkedAtoms (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  ((goldbachG12ActiveProductSupport N) ×ˢ range (N+1)).filter fun p =>
    p.2.Prime ∧ p.2.Coprime N ∧ (N : ℝ)^(4/53 : ℝ) < p.2 ∧
    p.2 ≤ p.1.minFac ∧ ε*N < (p.2 : ℝ)*p.1 ∧ p.2*p.1 < N

def low (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  (globalLinkedAtoms N ε).filter fun p => (p.2 : ℝ) < (N : ℝ)^(1/10 : ℝ)

def high (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  (globalLinkedAtoms N ε).filter fun p => (N : ℝ)^(1/10 : ℝ) ≤ (p.2 : ℝ)

def outputCount (N : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  400 * ∑ p ∈ S, goldbachG12NormalizedCoefficient N p.1 *
    (if (N-p.2*p.1).Prime then 1 else 0)

theorem low_eq_mother (N : ℕ) (ε : ℝ) : low N ε = G12LowRectangle.mother N ε := by
  ext p
  simp only [low, globalLinkedAtoms, G12LowRectangle.mother, mem_filter]
  tauto

theorem partition (N : ℕ) (ε : ℝ) :
    Disjoint (low N ε) (high N ε) ∧
      low N ε ∪ high N ε = globalLinkedAtoms N ε := by
  constructor
  · apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (mem_filter.mp hq).2) (mem_filter.mp hp).2
  · ext p
    simp only [low, high, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hp
      rcases lt_or_ge (p.2 : ℝ) ((N : ℝ)^(1/10 : ℝ)) with h | h
      · exact Or.inl ⟨hp,h⟩
      · exact Or.inr ⟨hp,h⟩

theorem boundary_in_high (N : ℕ) (ε : ℝ) (p : ℕ × ℕ)
    (hp : p ∈ globalLinkedAtoms N ε) (he : (p.2 : ℝ) = (N : ℝ)^(1/10 : ℝ)) :
    p ∈ high N ε ∧ p ∉ low N ε := by
  exact ⟨mem_filter.mpr ⟨hp, he.ge⟩,
    fun h => (not_lt_of_ge he.ge) (mem_filter.mp h).2⟩

/-- Exact real weighted splitting, without subtracting inequalities. -/
theorem weighted_partition (N : ℕ) (ε : ℝ) (f : ℕ × ℕ → ℝ) :
    (400 * ∑ p ∈ globalLinkedAtoms N ε, goldbachG12NormalizedCoefficient N p.1 * f p) =
      (400 * ∑ p ∈ low N ε, goldbachG12NormalizedCoefficient N p.1 * f p) +
      (400 * ∑ p ∈ high N ε, goldbachG12NormalizedCoefficient N p.1 * f p) := by
  obtain ⟨hd, hu⟩ := partition N ε
  rw [← hu, sum_union hd, mul_add]

theorem output_partition (N : ℕ) (ε : ℝ) :
    outputCount N (globalLinkedAtoms N ε) =
      outputCount N (low N ε) + outputCount N (high N ε) :=
  weighted_partition N ε _

/-- The low summand consumes the established original-fibre identity literally. -/
theorem original_low_count (N : ℕ) (ε : ℝ) :
    outputCount N (low N ε) =
    ∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ))).card : ℝ) := by
  rw [low_eq_mother]
  exact G12LowRectangle.original_low_count N ε

/-- The physical carrier has exactly the original output-prime fibres. -/
theorem global_output_iff (N m r : ℕ) (ε : ℝ) :
    ((m,r) ∈ globalLinkedAtoms N ε ∧ (N-r*m).Prime) ↔
      m ∈ goldbachG12ActiveProductSupport N ∧
        r ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m := by
  constructor
  · rintro ⟨hr,hout⟩
    obtain ⟨hbase,hp,hcop,hz,hfac,he,hn⟩ := mem_filter.mp hr
    have hm := (mem_product.mp hbase).1
    refine ⟨hm, ?_⟩
    rw [goldbachG11ProductFirstPrimeFiber_endpoint_iff
      (goldbachG12ActiveProductSupport_mem_full hm)]
    exact ⟨hp, hp.coprime_iff_not_dvd.mp hcop, hz, hfac,
      by simpa only [Nat.cast_mul] using he, hn.le, hout⟩
  · rintro ⟨hm,hr⟩
    rw [goldbachG11ProductFirstPrimeFiber_endpoint_iff
      (goldbachG12ActiveProductSupport_mem_full hm)] at hr
    obtain ⟨hp,hcop,hz,hfac,he,hn,hout⟩ := hr
    have hstrict : r*m < N := by have := hout.two_le; omega
    have hm0 := (goldbachG12ActiveProductSupport_data hm).1
    have hrN : r < N := (Nat.le_mul_of_pos_right r hm0).trans_lt hstrict
    refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hm, mem_range.mpr (by omega)⟩,
      hp, hp.coprime_iff_not_dvd.mpr hcop, hz, hfac, ?_, hstrict⟩, hout⟩
    simpa only [Nat.cast_mul] using he

/-- An exact finite identity for any first-prime test. This is not a
Siegel--Walfisz inheritance assertion for arbitrary filters. -/
theorem original_filtered_count (N : ℕ) (ε : ℝ) (P : ℕ → Prop) [DecidablePred P] :
    outputCount N ((globalLinkedAtoms N ε).filter (fun p => P p.2)) =
    ∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter P).card : ℝ) := by
  unfold outputCount
  rw [G12LowRectangle.restore_multiplicity]
  have hfilter : ((globalLinkedAtoms N ε).filter (fun p => P p.2)).filter
      (fun p => (N-p.2*p.1).Prime) =
      ((goldbachG12ActiveProductSupport N).sigma (fun m =>
        (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter P)).image
          (fun p : (_ : ℕ) × ℕ => (p.1,p.2)) := by
    ext ⟨m,r⟩
    simp only [mem_filter, mem_image, mem_sigma]
    have h := global_output_iff N m r ε
    constructor
    · rintro ⟨⟨hg,hP⟩,hp⟩
      obtain ⟨hm,hr⟩ := h.mp ⟨hg,hp⟩
      exact ⟨⟨m,r⟩, ⟨hm,hr,hP⟩, rfl⟩
    · rintro ⟨⟨m',r'⟩, ⟨hm,hr,hP⟩, he⟩
      cases he
      obtain ⟨hg,hp⟩ := h.mpr ⟨hm,hr⟩
      exact ⟨⟨hg,hP⟩,hp⟩
  calc
    _ = ∑ p ∈ ((globalLinkedAtoms N ε).filter (fun p => P p.2)).filter
        (fun p => (N-p.2*p.1).Prime),
        (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) p.1 : ℝ) := by
      simp only [sum_filter, mul_ite, mul_one, mul_zero]
    _ = _ := by
      rw [hfilter, sum_image]
      · rw [Finset.sum_sigma]
        apply sum_congr rfl
        intro m _
        simp [mul_comm]
      · intro a _ b _ hab
        cases a
        cases b
        obtain ⟨hm,hr⟩ := Prod.mk.inj hab
        cases hm
        cases hr
        rfl

theorem original_high_count (N : ℕ) (ε : ℝ) :
    outputCount N (high N ε) =
    ∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (N : ℝ)^(1/10 : ℝ) ≤ (r : ℝ))).card : ℝ) :=
  original_filtered_count N ε (fun r : ℕ => (N : ℝ)^(1/10 : ℝ) ≤ (r : ℝ))

/-- Exact splitting of the original integer G12 total, with coefficient/400
normalization restored on both physical output-prime summands. -/
theorem original_total_partition (N : ℕ) (ε : ℝ) (hN : 2 ≤ N) :
    (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) =
      outputCount N (low N ε) + outputCount N (high N ε) := by
  rw [← output_partition]
  have h := original_filtered_count N ε (fun _ => True)
  simp only [filter_true] at h
  rw [h, goldbachG12ProductPrimeTotal_eq_active N ε hN, mul_sum]
  apply sum_congr rfl
  intro m _
  unfold goldbachG12NormalizedCoefficient
  ring

/-- The ungated distribution carrier is kept separate from the original
coprime-gated physical output carrier. -/
def sourceLow (N : ℕ) (ε : ℝ) : Finset GoldbachG12LinkedAtom :=
  (goldbachG12LinkedAtoms N ε).filter fun p => (p.2 : ℝ) < (N : ℝ)^(1/10 : ℝ)

def sourceHigh (N : ℕ) (ε : ℝ) : Finset GoldbachG12LinkedAtom :=
  (goldbachG12LinkedAtoms N ε).filter fun p => (N : ℝ)^(1/10 : ℝ) ≤ (p.2 : ℝ)

theorem source_partition (N : ℕ) (ε : ℝ) :
    Disjoint (sourceLow N ε) (sourceHigh N ε) ∧
      sourceLow N ε ∪ sourceHigh N ε = goldbachG12LinkedAtoms N ε := by
  constructor
  · apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (mem_filter.mp hq).2) (mem_filter.mp hp).2
  · apply Finset.ext
    intro p
    simp only [sourceLow, sourceHigh, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hp
      rcases lt_or_ge (p.2 : ℝ) ((N : ℝ)^(1/10 : ℝ)) with h | h
      · exact Or.inl ⟨hp,h⟩
      · exact Or.inr ⟨hp,h⟩

/-- The original distribution atoms themselves split exactly for every real
weight test; this does not claim that a distribution bound splits. -/
theorem source_weighted_partition (N : ℕ) (ε : ℝ) (f : GoldbachG12LinkedAtom → ℝ) :
    (400 * ∑ p ∈ goldbachG12LinkedAtoms N ε, goldbachG12NormalizedCoefficient N p.1 * f p) =
      (400 * ∑ p ∈ sourceLow N ε, goldbachG12NormalizedCoefficient N p.1 * f p) +
      (400 * ∑ p ∈ sourceHigh N ε, goldbachG12NormalizedCoefficient N p.1 * f p) := by
  obtain ⟨hd, hu⟩ := source_partition N ε
  rw [← hu, Finset.sum_union hd, mul_add]

end G12LowHighOutput
