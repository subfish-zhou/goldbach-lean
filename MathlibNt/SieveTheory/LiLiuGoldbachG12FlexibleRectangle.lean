import MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangleC2

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12FlexibleRectangle

/-- The original physical mother and discrepancy, without changing N or epsilon. -/
abbrev mother := G12LowRectangle.mother
abbrev discrepancy := G12LowRectangle.discrepancy
abbrev beta := G12LowRectangle.beta

/-- Safety depends only on the long variable and the actual short endpoints. -/
def longOK (N : ℕ) (ε : ℝ) (T V m : ℕ) : Prop :=
  m ∈ goldbachG12ActiveProductSupport N ∧ V ≤ m.minFac ∧
    ε*N ≤ (T : ℝ)*m ∧ V*m < N

def longSet (N : ℕ) (ε : ℝ) (M U T V : ℕ) : Finset ℕ :=
  (Ioc M U).filter (longOK N ε T V)

def shortSet (N T V : ℕ) : Finset ℕ :=
  (Ioc T V).filter fun r => r.Prime ∧ r.Coprime N

def rectangle (N : ℕ) (ε : ℝ) (M U T V : ℕ) : Finset (ℕ × ℕ) :=
  (longSet N ε M U T V) ×ˢ (shortSet N T V)

def alpha (N : ℕ) (ε : ℝ) (T V m : ℕ) : ℝ :=
  if longOK N ε T V m then goldbachG12NormalizedCoefficient N m else 0

/-- This residual is retained; no estimate is claimed for it. -/
def boundary (N : ℕ) (ε : ℝ) (M U T V : ℕ) : Finset (ℕ × ℕ) :=
  mother N ε \ rectangle N ε M U T V

theorem alpha_bounds (N : ℕ) (ε : ℝ) (T V m : ℕ) :
    0 ≤ alpha N ε T V m ∧ alpha N ε T V m ≤ 1 := by
  unfold alpha
  split_ifs
  · exact goldbachG12NormalizedCoefficient_bounds N m
  · norm_num

theorem alpha_tau (N : ℕ) (ε : ℝ) (M U T V m : ℕ) (hm : m ∈ Ioc M U) :
    |alpha N ε T V m| ≤ (fouvryTau 1 m : ℝ) := by
  have hp : m ≠ 0 := by have := (mem_Ioc.mp hm).1; omega
  rw [fouvryTau_order_one hp, Nat.cast_one, abs_of_nonneg (alpha_bounds N ε T V m).1]
  exact (alpha_bounds N ε T V m).2

/-- The source scale remains T, even when V is arbitrarily close to T. -/
def shortInterval (T V : ℕ) (hT : 1 ≤ T) (hTV : T ≤ V) (hV : V ≤ 2*T) :
    PrimeC2Interval where
  scale := T
  lower := T
  upper := V
  one_le_scale := by exact_mod_cast hT
  scale_le_lower := le_rfl
  lower_le_upper := by exact_mod_cast hTV
  upper_le_twice := by exact_mod_cast hV

theorem shortInterval_support (T V : ℕ) (hT : 1 ≤ T) (hTV : T ≤ V)
    (hV : V ≤ 2*T) :
    primeSWInterval (shortInterval T V hT hTV hV).lower
      (shortInterval T V hT hTV hV).upper = Ioc T V := by
  change Ioc ⌊(T : ℝ)⌋₊ ⌊(V : ℝ)⌋₊ = Ioc T V
  rw [Nat.floor_natCast, Nat.floor_natCast]

/-- Actual endpoint geometry, not the enclosing dyadic geometry, gives coverage. -/
theorem rectangle_subset_mother (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (V : ℝ) < (N : ℝ)^(1/10 : ℝ)) :
    rectangle N ε M U T V ⊆ mother N ε := by
  rintro ⟨m,r⟩ hp
  obtain ⟨hm,hr⟩ := mem_product.mp hp
  obtain ⟨_, hs, hfac, he, hn⟩ := mem_filter.mp hm
  obtain ⟨hrI, hp, hc⟩ := mem_filter.mp hr
  obtain ⟨hTr, hrV⟩ := mem_Ioc.mp hrI
  have hm0 := (goldbachG12ActiveProductSupport_data hs).1
  have hrm : r*m < N := (Nat.mul_le_mul_right m hrV).trans_lt hn
  have hrN : r < N := (Nat.le_mul_of_pos_right r hm0).trans_lt hrm
  have hTrR : (T : ℝ) < r := by exact_mod_cast hTr
  have hrVR : (r : ℝ) ≤ V := by exact_mod_cast hrV
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨hs, mem_range.mpr (by omega)⟩, hp, hc,
    hlow.trans_lt hTrR, hrV.trans hfac, ?_, hrm, hrVR.trans_lt hhigh⟩
  exact he.trans_lt (mul_lt_mul_of_pos_right hTrR hmR)

/-- Within a cell the physical boundary is exactly the three failed safety tests. -/
theorem local_boundary_iff (N m r M U T V : ℕ) (ε : ℝ)
    (h : (m,r) ∈ mother N ε) (hm : m ∈ Ioc M U) (hr : r ∈ Ioc T V) :
    (m,r) ∈ boundary N ε M U T V ↔
      m.minFac < V ∨ (T : ℝ)*m < ε*N ∨ N ≤ V*m := by
  have hbase := (mem_product.mp (mem_filter.mp h).1).1
  have hp := (mem_filter.mp h).2.1
  have hc := (mem_filter.mp h).2.2.1
  dsimp only at hbase hp hc
  change r.gcd N = 1 at hc
  simp only [boundary, mem_sdiff, h, true_and, rectangle, mem_product,
    longSet, shortSet, mem_filter, hm, hr, longOK, hbase, hp, Nat.Coprime, hc,
    and_true, true_and, not_and_or, not_le, not_lt]

/-- Equality with the same normalized coefficient, before any modulus summation. -/
theorem rectangle_test (N : ℕ) (ε : ℝ) (M U T V : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ rectangle N ε M U T V,
      goldbachG12NormalizedCoefficient N p.1 * f p.1 p.2) =
      ∑ m ∈ Ioc M U, ∑ r ∈ Ioc T V, alpha N ε T V m * beta N r * f m r := by
  unfold rectangle
  rw [Finset.sum_product]
  unfold longSet shortSet
  simp only [Finset.sum_filter]
  apply sum_congr rfl
  intro m _
  by_cases hm : longOK N ε T V m
  · simp only [hm, ite_true]
    apply sum_congr rfl
    intro r _
    by_cases hp : r.Prime <;> by_cases hc : r.Coprime N <;>
      simp [alpha, beta, G12LowRectangle.beta, primeSWBeta, hm, hp, hc]
  · simp [alpha, hm]

/-- Full signed equality uses exactly the same moduli and c, preserving cancellation. -/
theorem rectangle_signedError (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (Q : Finset ℕ) (c : ℕ → ℝ) :
    discrepancy N (rectangle N ε M U T V) Q c =
      signedError (Ioc M U) (Ioc T V) Q
        (alpha N ε T V) (beta N) c (N : ℤ) := by
  unfold discrepancy G12LowRectangle.discrepancy signedError
  apply sum_congr rfl
  intro d _
  congr 1
  unfold bilinearDiscrepancy
  have htest (P : ℕ → ℕ → Prop) [DecidableRel P] :
      (∑ p ∈ rectangle N ε M U T V, if P p.1 p.2 then
        goldbachG12NormalizedCoefficient N p.1 else 0) =
      ∑ m ∈ Ioc M U, ∑ r ∈ Ioc T V,
        if P m r then alpha N ε T V m * beta N r else 0 := by
    simpa only [mul_ite, mul_one, mul_zero] using
      rectangle_test N ε M U T V (fun m r => if P m r then 1 else 0)
  exact congrArg₂ (fun x y : ℝ => x-y/(d.totient : ℝ))
    (htest (fun m r => Int.ModEq d ((m : ℤ)*r) (N : ℤ)))
    (htest (fun m r => (m*r).Coprime d))

theorem mother_partition (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (V : ℝ) < (N : ℝ)^(1/10 : ℝ)) :
    Disjoint (rectangle N ε M U T V) (boundary N ε M U T V) ∧
      rectangle N ε M U T V ∪ boundary N ε M U T V = mother N ε := by
  have hs := rectangle_subset_mother N ε M U T V hlow hhigh
  exact ⟨disjoint_sdiff_self_right, union_sdiff_of_subset hs⟩

/-- Body multiplicity 400 remains on both the inner and residual sums. -/
theorem weighted_partition (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (V : ℝ) < (N : ℝ)^(1/10 : ℝ)) (f : ℕ × ℕ → ℝ) :
    (400 * ∑ p ∈ mother N ε, goldbachG12NormalizedCoefficient N p.1 * f p) =
      (400 * ∑ p ∈ rectangle N ε M U T V,
        goldbachG12NormalizedCoefficient N p.1 * f p) +
      (400 * ∑ p ∈ boundary N ε M U T V,
        goldbachG12NormalizedCoefficient N p.1 * f p) := by
  obtain ⟨hd, hu⟩ := mother_partition N ε M U T V hlow hhigh
  rw [← hu, sum_union hd, mul_add]

theorem signed_partition (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (V : ℝ) < (N : ℝ)^(1/10 : ℝ))
    (Q : Finset ℕ) (c : ℕ → ℝ) :
    discrepancy N (mother N ε) Q c =
      signedError (Ioc M U) (Ioc T V) Q (alpha N ε T V) (beta N) c (N : ℤ) +
        discrepancy N (boundary N ε M U T V) Q c := by
  rw [← rectangle_signedError]
  obtain ⟨hd, hu⟩ := mother_partition N ε M U T V hlow hhigh
  unfold discrepancy G12LowRectangle.discrepancy
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← hu, sum_union hd, sum_union hd]
  ring

/-- The original low count splits with its full repeated-body coefficient.
The old mother-to-fibre identification is reused, not reproved. -/
theorem original_low_partition (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (V : ℝ) < (N : ℝ)^(1/10 : ℝ)) :
    (∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ))).card : ℝ)) =
      (400 * ∑ p ∈ rectangle N ε M U T V,
        goldbachG12NormalizedCoefficient N p.1 *
          (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
      (400 * ∑ p ∈ boundary N ε M U T V,
        goldbachG12NormalizedCoefficient N p.1 *
          (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) := by
  rw [← G12LowRectangle.original_low_count]
  exact weighted_partition N ε M U T V hlow hhigh _

/-- The old dyadic rectangle is a specialization, not a second physical mother. -/
theorem dyadic_specialization (N : ℕ) (ε : ℝ) (M T : ℕ) :
    rectangle N ε M (2*M) T (2*T) = G12LowRectangle.rectangle N ε M T := rfl

theorem mother_zero (ε : ℝ) : mother 0 ε = ∅ := G12LowRectangle.mother_zero ε

theorem rectangle_zero (ε : ℝ) (M U T V : ℕ) : rectangle 0 ε M U T V = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨m,r⟩ hp
  have hn := (mem_filter.mp (mem_product.mp hp).1).2.2.2.2
  omega

theorem rectangle_empty_long (N : ℕ) (ε : ℝ) (M T V : ℕ) :
    rectangle N ε M M T V = ∅ := by simp [rectangle, longSet]

theorem rectangle_empty_short (N : ℕ) (ε : ℝ) (M U T : ℕ) :
    rectangle N ε M U T T = ∅ := by simp [rectangle, shortSet]

theorem product_endpoint_excluded (N m r : ℕ) (ε : ℝ) (he : r*m = N) :
    (m,r) ∉ mother N ε := G12LowRectangle.product_endpoint_excluded N m r ε he

end G12FlexibleRectangle
