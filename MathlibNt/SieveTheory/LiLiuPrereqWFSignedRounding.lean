import MathlibNt.SieveTheory.LiLiuPrereqWFRoundedAdmissibility

/-!
# Finite sieve direction for one normalized signed box convention

The positive/negative choices are those of Iwaniec (17)--(18): the
favourable sign uses weakly decreasing boxes at the original level; the
opposite sign uses distinct boxes and the upper endpoints. Each squarefree
prime set contributes once. This is the divided-power convention, NOT the
raw labelled-slot sum or its factorial-copy expansion.

The two endpoint functions enclose each prime. The exact geometric
specialization and identification with the common full-integer box weights
are separate from the pointwise sieve inequalities proved here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

/-- Rounded strict support and all source cubic tests. -/
def RoundedSupport (upper : Bool) (b : ℕ → ℝ) (D : ℝ) (s : Finset ℕ) : Prop :=
  (∏ p ∈ s, b p) < D ∧ RoundedSetAdmissible upper b D s

theorem roundedSupport_mono {upper : Bool} {b c : ℕ → ℝ} {D : ℝ}
    {s : Finset ℕ} (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbc : ∀ p ∈ s, b p ≤ c p) (h : RoundedSupport upper c D s) :
    RoundedSupport upper b D s := by
  refine ⟨lt_of_le_of_lt (Finset.prod_le_prod hb hbc) h.1, ?_⟩
  intro p hp hpar
  apply lt_of_le_of_lt _ (h.2 p hp hpar)
  apply mul_le_mul
  · exact Finset.prod_le_prod
      (fun q hq => hb q (Finset.mem_filter.mp hq).1)
      (fun q hq => hbc q (Finset.mem_filter.mp hq).1)
  · exact pow_le_pow_left₀ (hb p hp) (hbc p hp) 2
  · exact sq_nonneg _
  · exact Finset.prod_nonneg
      (fun q hq => (hb q (Finset.mem_filter.mp hq).1).trans
        (hbc q (Finset.mem_filter.mp hq).1))

theorem roundedSupport_cast_lower_iff (D : ℝ) (s : Finset ℕ) :
    RoundedSupport false (fun p : ℕ => (p : ℝ)) D s ↔
      ((s.prod id : ℕ) : ℝ) < D ∧ SmallRosser.LowerAdmissibleSet D s := by
  simp only [RoundedSupport, roundedSetAdmissible_cast_lower_iff, Nat.cast_prod, id_eq]

theorem roundedSupport_cast_upper_iff (D : ℝ) (s : Finset ℕ) :
    RoundedSupport true (fun p : ℕ => (p : ℝ)) D s ↔
      ((s.prod id : ℕ) : ℝ) < D ∧ SmallRosser.UpperAdmissibleSet D s := by
  simp only [RoundedSupport, roundedSetAdmissible_cast_upper_iff, Nat.cast_prod, id_eq]

/-- The source's strictly decreasing-box side, before the sign is applied. -/
def TightRoundedSupport (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (s : Finset ℕ) : Prop :=
  Set.InjOn b (↑s : Set ℕ) ∧ RoundedSupport upper c D s

noncomputable def normalizedUpperSet (b c : ℕ → ℝ) (D : ℝ)
    (s : Finset ℕ) : ℝ :=
  if Even s.card then
    if RoundedSupport true b D s then 1 else 0
  else
    if TightRoundedSupport true b c D s then -1 else 0

noncomputable def normalizedLowerSet (b c : ℕ → ℝ) (D : ℝ)
    (s : Finset ℕ) : ℝ :=
  if Even s.card then
    if TightRoundedSupport false b c D s then 1 else 0
  else
    if RoundedSupport false b D s then -1 else 0

/-- Removing negative terms or adding positive terms only raises the upper
Rosser coefficient. Repeated-box prime sets are still counted exactly once. -/
theorem upperSetWeight_le_normalizedUpperSet {b c : ℕ → ℝ} {D : ℝ}
    {s : Finset ℕ} (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbp : ∀ p ∈ s, b p ≤ (p : ℝ)) (hpc : ∀ p ∈ s, (p : ℝ) ≤ c p) :
    SmallRosser.upperSetWeight D s ≤ normalizedUpperSet b c D s := by
  have hlo :
      (((s.prod id : ℕ) : ℝ) < D ∧ SmallRosser.UpperAdmissibleSet D s) →
        RoundedSupport true b D s :=
    fun h => roundedSupport_mono hb hbp ((roundedSupport_cast_upper_iff D s).mpr h)
  have hhi : TightRoundedSupport true b c D s →
      ((s.prod id : ℕ) : ℝ) < D ∧ SmallRosser.UpperAdmissibleSet D s :=
    fun h => (roundedSupport_cast_upper_iff D s).mp
      (roundedSupport_mono (fun p _ => Nat.cast_nonneg p) hpc h.2)
  unfold SmallRosser.upperSetWeight normalizedUpperSet
  split_ifs <;> simp_all
  linarith

/-- The lower sign reverses BOTH choices: odd terms are enlarged, while
positive even terms with a repeated box are omitted. -/
theorem normalizedLowerSet_le_setWeight {b c : ℕ → ℝ} {D : ℝ}
    {s : Finset ℕ} (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbp : ∀ p ∈ s, b p ≤ (p : ℝ)) (hpc : ∀ p ∈ s, (p : ℝ) ≤ c p) :
    normalizedLowerSet b c D s ≤ SmallRosser.setWeight D s := by
  have hlo :
      (((s.prod id : ℕ) : ℝ) < D ∧ SmallRosser.LowerAdmissibleSet D s) →
        RoundedSupport false b D s :=
    fun h => roundedSupport_mono hb hbp ((roundedSupport_cast_lower_iff D s).mpr h)
  have hhi : TightRoundedSupport false b c D s →
      ((s.prod id : ℕ) : ℝ) < D ∧ SmallRosser.LowerAdmissibleSet D s :=
    fun h => (roundedSupport_cast_lower_iff D s).mp
      (roundedSupport_mono (fun p _ => Nat.cast_nonneg p) hpc h.2)
  unfold SmallRosser.setWeight normalizedLowerSet
  split_ifs <;> simp_all
  linarith


end MathlibNt.SieveTheory.LiLiuPrereqWF
