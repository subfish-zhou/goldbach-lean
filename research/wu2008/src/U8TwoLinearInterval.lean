import U8TwoLinearCRT
import Mathlib.Data.Int.CardIntervalMod

noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct

/-- The literal filtered interval is an integer interval, including empty and closed-cut cases. -/
theorem interval_eq_Ico (N : ℕ) (e : ℝ) (t : ℕ × ℕ) :
    ∃ L U : ℕ, L ≤ U ∧ interval N e t = Ico L U := by
  classical
  by_cases h : (interval N e t).Nonempty
  · let L := (interval N e t).min' h
    let M := (interval N e t).max' h
    have hL : L ∈ interval N e t := min'_mem _ h
    have hM : M ∈ interval N e t := max'_mem _ h
    have hLM : L ≤ M := le_max' _ _ hL
    refine ⟨L, M+1, by omega, ?_⟩
    ext r
    constructor
    · intro hr
      exact mem_Ico.mpr ⟨min'_le _ _ hr, by have := le_max' _ _ hr; omega⟩
    · intro hr
      obtain ⟨hLr,hrM⟩ := mem_Ico.mp hr
      have hrM' : r ≤ M := by omega
      obtain ⟨hMN,_,hMN',hMe⟩ := mem_filter.mp hM
      have hbr := (mem_filter.mp hL).2.1
      have hmul := Nat.mul_le_mul_left (t.1*t.2) hrM'
      have hmulR : ((t.1*t.2*r : ℕ) : ℝ) ≤ (t.1*t.2*M : ℕ) := by exact_mod_cast hmul
      exact mem_filter.mpr ⟨mem_range.mpr (hrM'.trans_lt (mem_range.mp hMN)),
        hbr.trans hLr, hmul.trans_lt hMN', hmulR.trans hMe⟩
  · exact ⟨0,0,le_rfl, by rw [not_nonempty_iff_eq_empty.mp h]; simp⟩

/-- A single residue in a prefix differs from length/modulus by at most one. -/
theorem prefix_modEq_error (b v m : ℕ) (hm : 0 < m) :
    |((b.count (· ≡ v [MOD m]) : ℕ) : ℝ) - (b : ℝ)/m| ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrem0 : (0 : ℝ) ≤ (b % m : ℕ) := Nat.cast_nonneg _
  have hrem : ((b % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt b hm
  have heq : (b : ℝ) = (b / m : ℕ) * (m : ℝ) + (b % m : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' b m).symm
  have hdiv : (b : ℝ) / m * m = b := div_mul_cancel₀ _ hmR.ne'
  rw [Nat.count_modEq_card b hm v]
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> nlinarith

/-- Explicit subtraction of nested prefix counts, with its natural-subtraction guard. -/
theorem Ico_filter_card_sub (L U : ℕ) (hLU : L ≤ U) (P : ℕ → Prop) [DecidablePred P] :
    ((Ico L U).filter P).card = U.count P - L.count P := by
  have hs : (range L).filter P ⊆ (range U).filter P :=
    filter_subset_filter _ (range_mono hLU)
  have he : (Ico L U).filter P = (range U).filter P \ (range L).filter P := by
    ext r
    simp only [mem_filter, mem_Ico, mem_sdiff, mem_range]
    by_cases hr : P r <;> simp only [hr, and_true, and_false, not_false_eq_true]
    omega
  rw [he, card_sdiff_of_subset hs, ← Nat.count_eq_card_filter_range,
    ← Nat.count_eq_card_filter_range]

/-- Two prefix endpoint errors give a uniform, closed bound for every integer interval. -/
theorem Ico_modEq_error (L U v m : ℕ) (hLU : L ≤ U) (hm : 0 < m) :
    |((((Ico L U).filter (· ≡ v [MOD m])).card : ℕ) : ℝ) -
      ((U-L : ℕ) : ℝ)/m| ≤ 2 := by
  have hcnt := Nat.count_monotone (p := (· ≡ v [MOD m])) hLU
  rw [Ico_filter_card_sub L U hLU, Nat.cast_sub hcnt, Nat.cast_sub hLU, sub_div]
  have heq : (U.count (· ≡ v [MOD m]) : ℝ) - L.count (· ≡ v [MOD m]) -
      ((U : ℝ)/m-(L : ℝ)/m) =
      ((U.count (· ≡ v [MOD m]) : ℝ)-(U : ℝ)/m) -
      ((L.count (· ≡ v [MOD m]) : ℝ)-(L : ℝ)/m) := by ring
  rw [heq]
  have hb := (abs_sub _ _).trans (add_le_add (prefix_modEq_error U v m hm)
    (prefix_modEq_error L v m hm))
  norm_num only [one_add_one_eq_two] at hb
  exact hb

/-- Residue-class error on the actual interval; X is its cardinality. -/
theorem interval_class_error (N m : ℕ) [NeZero m] (e : ℝ) (t : ℕ × ℕ) (v : ZMod m) :
    |(((interval N e t).filter fun r : ℕ => (r : ZMod m) = v).card : ℝ) -
      ((interval N e t).card : ℝ)/m| ≤ 2 := by
  obtain ⟨L,U,hLU,hI⟩ := interval_eq_Ico N e t
  have hpred (r : ℕ) : (r : ZMod m) = v ↔ r ≡ v.val [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  simp_rw [hI, hpred]
  rw [Nat.card_Ico]
  exact Ico_modEq_error L U v.val m hLU (Nat.pos_of_ne_zero (NeZero.ne m))

/-- Actual root finset for a nonzero composite modulus. -/
def residueRoots (m N a : ℕ) [NeZero m] : Finset (ZMod m) := by
  classical
  exact univ.filter fun x => x*((N : ZMod m)-(a : ZMod m)*x)=0

theorem residueRoots_card (m N a : ℕ) [NeZero m] :
    (residueRoots m N a).card = residueRootCount m N a := by
  classical
  simp only [residueRoots, residueRootCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem residueRootCount_le (m N a : ℕ) [NeZero m] : residueRootCount m N a ≤ m := by
  rw [← residueRoots_card]
  exact (card_filter_le _ _).trans_eq (by simp [ZMod.card])

/-- The natural subtraction in twoLinear is transported only where a*r < N. -/
theorem twoLinear_dvd_iff_residue {m N r : ℕ} [NeZero m]
    {e : ℝ} {t : ℕ × ℕ} (hr : r ∈ interval N e t) :
    m ∣ twoLinear N t r ↔ (r : ZMod m) ∈ residueRoots m N (t.1*t.2) := by
  have hprod := (mem_filter.mp hr).2.2.1
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [twoLinear, residueRoots, mem_filter, mem_univ, true_and]
  rw [Nat.cast_mul, Nat.cast_sub hprod.le]
  simp only [Nat.cast_mul]

/-- Disjoint residue fibers give an exact sum, not independent random events. -/
theorem interval_residue_count (N m : ℕ) [NeZero m] (e : ℝ) (t : ℕ × ℕ)
    (S : Finset (ZMod m)) :
    ((interval N e t).filter fun r : ℕ => (r : ZMod m) ∈ S).card =
      ∑ v ∈ S, ((interval N e t).filter fun r : ℕ => (r : ZMod m) = v).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun r : ℕ => (r : ZMod m))
    (s := (interval N e t).filter fun r : ℕ => (r : ZMod m) ∈ S)
    (t := S) (fun r hr => (mem_filter.mp hr).2)]
  apply sum_congr rfl
  intro v hv
  congr 1
  ext r
  simp only [mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,h.2 ▸ hv⟩,h.2⟩

/-- Genuine O(card S) error for any union of residue classes on the original interval. -/
theorem interval_residue_error (N m : ℕ) [NeZero m] (e : ℝ) (t : ℕ × ℕ)
    (S : Finset (ZMod m)) :
    |(((interval N e t).filter fun r : ℕ => (r : ZMod m) ∈ S).card : ℝ) -
      (interval N e t).card * (S.card : ℝ)/m| ≤ 2*(S.card : ℝ) := by
  classical
  rw [interval_residue_count, Nat.cast_sum]
  have he : (∑ v ∈ S, (((interval N e t).filter fun r : ℕ => (r : ZMod m) = v).card : ℝ)) -
      (interval N e t).card * (S.card : ℝ)/m =
      ∑ v ∈ S, ((((interval N e t).filter fun r : ℕ => (r : ZMod m) = v).card : ℝ) -
        ((interval N e t).card : ℝ)/m) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ∑ v ∈ S, |((((interval N e t).filter fun r : ℕ => (r : ZMod m) = v).card : ℝ) -
        ((interval N e t).card : ℝ)/m)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, (2 : ℝ) := sum_le_sum fun v _ => interval_class_error N m e t v
    _ = _ := by simp [mul_comm]

/-- Intersection divisibility is one modulus, lcm(d,f), and its exact CRT root count. -/
theorem divisibilityCount_error (N d f : ℕ) (hd : d ≠ 0) (hf : f ≠ 0)
    (e : ℝ) (t : ℕ × ℕ) :
    |(divisibilityCount N e t d f : ℝ) - (interval N e t).card *
      (residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ)/(Nat.lcm d f)| ≤
      2*(residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ) := by
  classical
  have : NeZero (Nat.lcm d f) := ⟨Nat.lcm_ne_zero hd hf⟩
  have he : ((interval N e t).filter fun r => d ∣ twoLinear N t r ∧ f ∣ twoLinear N t r) =
      (interval N e t).filter fun r : ℕ =>
        (r : ZMod (Nat.lcm d f)) ∈ residueRoots (Nat.lcm d f) N (t.1*t.2) := by
    apply filter_congr
    intro r hr
    rw [← Nat.lcm_dvd_iff, twoLinear_dvd_iff_residue hr]
  unfold divisibilityCount
  rw [he, ← residueRoots_card]
  exact interval_residue_error N (Nat.lcm d f) e t _

end U8Literal.SmallProduct
