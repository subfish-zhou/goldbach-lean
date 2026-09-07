import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindow
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKGoldbachRectangle

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12LowRectangle

/-- The physical low-r mother before testing primality of the output.
The upper product endpoint is strict; the body multiplicity is not collapsed. -/
def mother (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  ((goldbachG12ActiveProductSupport N) ×ˢ (range (N+1))).filter fun p =>
    p.2.Prime ∧ p.2.Coprime N ∧ (N : ℝ)^(4/53 : ℝ) < p.2 ∧
    p.2 ≤ p.1.minFac ∧ ε*N < (p.2 : ℝ)*p.1 ∧ p.2*p.1 < N ∧
    (p.2 : ℝ) < (N : ℝ)^(1/10 : ℝ)

/-- Long-only safety filter: every short point in (T,2T] stays in the curves. -/
def longOK (N : ℕ) (ε : ℝ) (T m : ℕ) : Prop :=
  m ∈ goldbachG12ActiveProductSupport N ∧ 2*T ≤ m.minFac ∧
    ε*N ≤ (T : ℝ)*m ∧ (2*T)*m < N

def longSet (N : ℕ) (ε : ℝ) (M T : ℕ) : Finset ℕ :=
  (Ioc M (2*M)).filter (longOK N ε T)

def shortSet (N T : ℕ) : Finset ℕ :=
  (Ioc T (2*T)).filter fun r => r.Prime ∧ r.Coprime N

def rectangle (N : ℕ) (ε : ℝ) (M T : ℕ) : Finset (ℕ × ℕ) :=
  (longSet N ε M T) ×ˢ (shortSet N T)

/-- This coefficient is independent of the short variable and the modulus. -/
def alpha (N : ℕ) (ε : ℝ) (T m : ℕ) : ℝ :=
  if longOK N ε T m then goldbachG12NormalizedCoefficient N m else 0

def beta (N r : ℕ) : ℝ := if r.Coprime N then primeSWBeta r else 0

/-- Exact signed finite discrepancy; no absolute value is taken inside either sum. -/
def discrepancy (N : ℕ) (S : Finset (ℕ × ℕ)) (Q : Finset ℕ)
    (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ reducedModuli Q (N : ℤ), c d *
    ((∑ p ∈ S, if Int.ModEq d ((p.1 : ℤ)*p.2) (N : ℤ)
        then goldbachG12NormalizedCoefficient N p.1 else 0) -
      (∑ p ∈ S, if (p.1*p.2).Coprime d
        then goldbachG12NormalizedCoefficient N p.1 else 0) / (d.totient : ℝ))

/-- The explicit unprocessed boundary, not an analytic error hypothesis. -/
def boundary (N : ℕ) (ε : ℝ) (M T : ℕ) : Finset (ℕ × ℕ) :=
  mother N ε \ rectangle N ε M T

theorem alpha_bounds (N : ℕ) (ε : ℝ) (T m : ℕ) :
    0 ≤ alpha N ε T m ∧ alpha N ε T m ≤ 1 := by
  unfold alpha
  split_ifs
  · exact goldbachG12NormalizedCoefficient_bounds N m
  · norm_num

theorem alpha_tau (N : ℕ) (ε : ℝ) (M T m : ℕ) (hm : m ∈ Ioc M (2*M)) :
    |alpha N ε T m| ≤ (fouvryTau 1 m : ℝ) := by
  have hp : m ≠ 0 := by have := (mem_Ioc.mp hm).1; omega
  rw [fouvryTau_order_one hp, Nat.cast_one, abs_of_nonneg (alpha_bounds N ε T m).1]
  exact (alpha_bounds N ε T m).2

theorem mother_zero (ε : ℝ) : mother 0 ε = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := (mem_filter.mp hp).2.2.2.2.2.2.1
  omega

/-- A dyadic interval in the exact C2 interval family. -/
def shortInterval (T : ℕ) (hT : 1 ≤ T) : PrimeC2Interval where
  scale := T
  lower := T
  upper := 2*T
  one_le_scale := by exact_mod_cast hT
  scale_le_lower := le_rfl
  lower_le_upper := by nlinarith [Nat.cast_nonneg (α := ℝ) T]
  upper_le_twice := le_rfl

theorem shortInterval_support (T : ℕ) (hT : 1 ≤ T) :
    primeSWInterval (shortInterval T hT).lower (shortInterval T hT).upper =
      Ioc T (2*T) := by
  change Ioc ⌊(T : ℝ)⌋₊ ⌊2*(T : ℝ)⌋₊ = Ioc T (2*T)
  have he : 2*(T : ℝ) = ((2*T : ℕ) : ℝ) := by push_cast; rfl
  rw [he, Nat.floor_natCast, Nat.floor_natCast]

/-- Exact inner coverage, with only explicit endpoint geometry as assumptions. -/
theorem rectangle_subset_mother (N : ℕ) (ε : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ)) :
    rectangle N ε M T ⊆ mother N ε := by
  rintro ⟨m,r⟩ hp
  obtain ⟨hm,hr⟩ := mem_product.mp hp
  obtain ⟨_, hs, hfac, he, hn⟩ := mem_filter.mp hm
  obtain ⟨hrI, hp, hc⟩ := mem_filter.mp hr
  obtain ⟨hTr, hrT⟩ := mem_Ioc.mp hrI
  have hm0 := (goldbachG12ActiveProductSupport_data hs).1
  have hrm : r*m < N := (Nat.mul_le_mul_right m hrT).trans_lt hn
  have hrN : r < N := (Nat.le_mul_of_pos_right r hm0).trans_lt hrm
  have hTrR : (T : ℝ) < r := by exact_mod_cast hTr
  have hrTR : (r : ℝ) ≤ (2*T : ℕ) := by exact_mod_cast hrT
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨hs, mem_range.mpr (by omega)⟩, hp, hc,
    hlow.trans_lt hTrR, hrT.trans hfac, ?_, hrm, hrTR.trans_lt hhigh⟩
  exact he.trans_lt (mul_lt_mul_of_pos_right hTrR hmR)

/-- The filtered product really has the same long coefficient as C2. -/
theorem rectangle_test (N : ℕ) (ε : ℝ) (M T : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ rectangle N ε M T, goldbachG12NormalizedCoefficient N p.1 * f p.1 p.2) =
      ∑ m ∈ Ioc M (2*M), ∑ r ∈ Ioc T (2*T), alpha N ε T m * beta N r * f m r := by
  unfold rectangle
  rw [Finset.sum_product]
  unfold longSet shortSet
  simp only [Finset.sum_filter]
  apply sum_congr rfl
  intro m _
  by_cases hm : longOK N ε T m
  · simp only [hm, ite_true]
    apply sum_congr rfl
    intro r _
    by_cases hp : r.Prime <;> by_cases hc : r.Coprime N <;>
      simp [alpha, beta, primeSWBeta, hm, hp, hc]
  · simp [alpha, hm]

/-- Signed discrepancy equality preserves cancellation across all moduli. -/
theorem rectangle_signedError (N : ℕ) (ε : ℝ) (M T : ℕ)
    (Q : Finset ℕ) (c : ℕ → ℝ) :
    discrepancy N (rectangle N ε M T) Q c =
      signedError (Ioc M (2*M)) (Ioc T (2*T)) Q
        (alpha N ε T) (beta N) c (N : ℤ) := by
  unfold discrepancy signedError
  apply sum_congr rfl
  intro d _
  congr 1
  unfold bilinearDiscrepancy
  have htest (P : ℕ → ℕ → Prop) [DecidableRel P] :
      (∑ p ∈ rectangle N ε M T, if P p.1 p.2 then
        goldbachG12NormalizedCoefficient N p.1 else 0) =
      ∑ m ∈ Ioc M (2*M), ∑ r ∈ Ioc T (2*T),
        if P m r then alpha N ε T m * beta N r else 0 := by
    simpa only [mul_ite, mul_one, mul_zero] using
      rectangle_test N ε M T (fun m r => if P m r then 1 else 0)
  exact congrArg₂ (fun x y : ℝ => x-y/(d.totient : ℝ))
    (htest (fun m r => Int.ModEq d ((m : ℤ)*r) (N : ℤ)))
    (htest (fun m r => (m*r).Coprime d))

/-- This is the literal C2 input, not a tuplewise absolute-error majorant. -/
theorem rectangle_C2_input (N : ℕ) (ε : ℝ) (M T : ℕ) (hT : 1 ≤ T)
    (Q : Finset ℕ) (c : ℕ → ℝ) :
    discrepancy N (rectangle N ε M T) Q c =
      signedError (Ioc M (2*M))
        (primeSWInterval (shortInterval T hT).lower (shortInterval T hT).upper)
        Q (alpha N ε T) (fun r => if r.Coprime N then primeSWBeta r else 0)
        c (N : ℤ) := by
  rw [shortInterval_support]
  exact rectangle_signedError N ε M T Q c

/-- Every atom is either in the certified rectangle or in the displayed boundary. -/
theorem mother_partition (N : ℕ) (ε : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ)) :
    Disjoint (rectangle N ε M T) (boundary N ε M T) ∧
      rectangle N ε M T ∪ boundary N ε M T = mother N ε := by
  have hs := rectangle_subset_mother N ε M T hlow hhigh
  exact ⟨disjoint_sdiff_self_right, union_sdiff_of_subset hs⟩

/-- Exact boundary membership displays each failed long-only safety condition. -/
theorem mem_boundary (N : ℕ) (ε : ℝ) (M T m r : ℕ) :
    (m,r) ∈ boundary N ε M T ↔ (m,r) ∈ mother N ε ∧
      ¬ (M < m ∧ m ≤ 2*M ∧ longOK N ε T m ∧ T < r ∧ r ≤ 2*T ∧
        r.Prime ∧ r.Coprime N) := by
  unfold boundary rectangle
  rw [mem_sdiff, Finset.mem_product]
  simp only [longSet, shortSet, mem_filter, mem_Ioc]
  tauto

/-- Any real test, including the output-prime indicator, has this exact partition. -/
theorem weighted_partition (N : ℕ) (ε : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ)) (f : ℕ × ℕ → ℝ) :
    (400 * ∑ p ∈ mother N ε, goldbachG12NormalizedCoefficient N p.1 * f p) =
      (400 * ∑ p ∈ rectangle N ε M T, goldbachG12NormalizedCoefficient N p.1 * f p) +
      (400 * ∑ p ∈ boundary N ε M T, goldbachG12NormalizedCoefficient N p.1 * f p) := by
  obtain ⟨hd, hu⟩ := mother_partition N ε M T hlow hhigh
  rw [← hu, sum_union hd, mul_add]

/-- The boundary discrepancy is retained with its sign, not asserted to be small. -/
theorem signed_partition (N : ℕ) (ε : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ))
    (Q : Finset ℕ) (c : ℕ → ℝ) :
    discrepancy N (mother N ε) Q c =
      signedError (Ioc M (2*M)) (Ioc T (2*T)) Q (alpha N ε T) (beta N) c (N : ℤ) +
        discrepancy N (boundary N ε M T) Q c := by
  rw [← rectangle_signedError]
  obtain ⟨hd, hu⟩ := mother_partition N ε M T hlow hhigh
  unfold discrepancy
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← hu, sum_union hd, sum_union hd]
  ring

/-- Literal correspondence with the original first-prime fibre, including its
output-prime test. No ambient-size hypothesis or new primality of k is required. -/
theorem mother_output_iff (N m r : ℕ) (ε : ℝ) :
    ((m,r) ∈ mother N ε ∧ (N-r*m).Prime) ↔
      m ∈ goldbachG12ActiveProductSupport N ∧
        r ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m ∧
        (r : ℝ) < (N : ℝ)^(1/10 : ℝ) := by
  constructor
  · rintro ⟨hr,hout⟩
    obtain ⟨hbase,hp,hcop,hz,hfac,he,hn,hlow⟩ := mem_filter.mp hr
    have hm := (mem_product.mp hbase).1
    refine ⟨hm, ?_, hlow⟩
    rw [goldbachG11ProductFirstPrimeFiber_endpoint_iff
      (goldbachG12ActiveProductSupport_mem_full hm)]
    exact ⟨hp, hp.coprime_iff_not_dvd.mp hcop, hz, hfac,
      by simpa only [Nat.cast_mul] using he, hn.le, hout⟩
  · rintro ⟨hm,hr,hlow⟩
    rw [goldbachG11ProductFirstPrimeFiber_endpoint_iff
      (goldbachG12ActiveProductSupport_mem_full hm)] at hr
    obtain ⟨hp,hcop,hz,hfac,he,hn,hout⟩ := hr
    have hstrict : r*m < N := by
      have := hout.two_le
      omega
    have hm0 := (goldbachG12ActiveProductSupport_data hm).1
    have hrN : r < N := (Nat.le_mul_of_pos_right r hm0).trans_lt hstrict
    refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hm, mem_range.mpr (by omega)⟩,
      hp, hp.coprime_iff_not_dvd.mpr hcop, hz, hfac, ?_, hstrict, hlow⟩, hout⟩
    simpa only [Nat.cast_mul] using he

/-- All original repeated body representations are restored, for any test. -/
theorem restore_multiplicity (N : ℕ) (S : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (400 * ∑ p ∈ S, goldbachG12NormalizedCoefficient N p.1 * f p) =
      ∑ p ∈ S, (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) p.1 : ℝ) * f p := by
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  unfold goldbachG12NormalizedCoefficient
  ring

/-- The exact low part of the original weighted product-fibre count. -/
theorem original_low_count (N : ℕ) (ε : ℝ) :
    (400 * ∑ p ∈ mother N ε, goldbachG12NormalizedCoefficient N p.1 *
      (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) =
    ∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ))).card : ℝ) := by
  rw [restore_multiplicity]
  have hfilter : (mother N ε).filter (fun p : ℕ × ℕ => (N-p.2*p.1).Prime) =
      ((goldbachG12ActiveProductSupport N).sigma (fun m =>
        (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
          (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ)))).image
            (fun p : (_ : ℕ) × ℕ => (p.1,p.2)) := by
    ext ⟨m,r⟩
    simp only [mem_filter, mem_image, mem_sigma]
    rw [mother_output_iff]
    constructor
    · rintro ⟨hm,hr,hlow⟩
      exact ⟨⟨m,r⟩, ⟨hm,hr,hlow⟩, rfl⟩
    · rintro ⟨⟨m,r⟩, ⟨hm,hr,hlow⟩, he⟩
      cases he
      exact ⟨hm,hr,hlow⟩
  calc
    _ = ∑ p ∈ (mother N ε).filter (fun p => (N-p.2*p.1).Prime),
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

/-- Within the same geometric cell, the residual is exactly a failed safe
least-factor or product-endpoint screen; none is paid for free. -/
theorem local_boundary_iff (N m r M T : ℕ) (ε : ℝ)
    (h : (m,r) ∈ mother N ε) (hm : m ∈ Ioc M (2*M)) (hr : r ∈ Ioc T (2*T)) :
    (m,r) ∈ boundary N ε M T ↔
      m.minFac < 2*T ∨ (T : ℝ)*m < ε*N ∨ N ≤ (2*T)*m := by
  have hbase := (mem_product.mp (mem_filter.mp h).1).1
  have hp := (mem_filter.mp h).2.1
  have hc := (mem_filter.mp h).2.2.1
  dsimp only at hbase hp hc
  change r.gcd N = 1 at hc
  rw [mem_boundary]
  simp only [h, true_and, longOK, hbase, (mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2,
    (mem_Ioc.mp hr).1, (mem_Ioc.mp hr).2, hp, Nat.Coprime, hc, and_true, true_and]
  simp only [not_and_or, not_le, not_lt]

theorem product_endpoint_excluded (N m r : ℕ) (ε : ℝ) (he : r*m = N) :
    (m,r) ∉ mother N ε := by
  intro h
  have hn := (mem_filter.mp h).2.2.2.2.2.2.1
  change r*m < N at hn
  omega

theorem long_support_geometry (M m : ℕ) (hm : m ∈ Ioc M (2*M)) :
    (M : ℝ) ≤ m ∧ (m : ℝ) ≤ 2*M := by
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hm
  constructor
  · exact_mod_cast hlo.le
  · exact_mod_cast hhi

/-- The genuine linked prime window, before output primality, with the
strict upper product endpoint recorded explicitly rather than silently deleted. -/
theorem mother_linked_iff (N m r : ℕ) (ε : ℝ) :
    (m,r) ∈ mother N ε ↔ m ∈ goldbachG12ActiveProductSupport N ∧
      r ∈ goldbachG11LinkedPrimeWindow N ε m ∧ r.Coprime N ∧
      r*m < N ∧ (r : ℝ) < (N : ℝ)^(1/10 : ℝ) := by
  constructor
  · intro h
    obtain ⟨hbase,hp,hc,hz,hfac,he,hn,hlow⟩ := mem_filter.mp h
    obtain ⟨hm,hr⟩ := mem_product.mp hbase
    have hmR : (0 : ℝ) < m := by
      exact_mod_cast (goldbachG12ActiveProductSupport_data hm).1
    have hfacR : (r : ℝ) ≤ m.minFac := by exact_mod_cast hfac
    have hnR : (r : ℝ)*(m : ℝ) ≤ N := by exact_mod_cast hn.le
    have hhi : (r : ℝ) ≤ goldbachG11PiLiHi N m :=
      le_min hfacR ((le_div_iff₀ hmR).mpr hnR)
    have hmax : max ((N : ℝ)^(4/53 : ℝ)) (ε*N/m) < r :=
      max_lt hz ((div_lt_iff₀ hmR).mpr he)
    have hlo : goldbachG11PiLiLo N ε m < r := (min_le_right _ _).trans_lt hmax
    exact ⟨hm, mem_filter.mpr ⟨hr,hp,hlo,hhi⟩,hc,hn,hlow⟩
  · rintro ⟨hm,hr,hc,hn,hlow⟩
    obtain ⟨hrange,hp,hlo,hhi⟩ := mem_filter.mp hr
    have hmR : (0 : ℝ) < m := by
      exact_mod_cast (goldbachG12ActiveProductSupport_data hm).1
    have hmax : max ((N : ℝ)^(4/53 : ℝ)) (ε*N/m) < r := by
      rcases min_lt_iff.mp hlo with hbad | hgood
      · exact False.elim ((not_lt_of_ge hhi) hbad)
      · exact hgood
    have hfac : r ≤ m.minFac := by
      exact_mod_cast (le_min_iff.mp hhi).1
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm,hrange⟩,hp,hc,
      (le_max_left _ _).trans_lt hmax,hfac,
      (div_lt_iff₀ hmR).mp ((le_max_right _ _).trans_lt hmax),hn,hlow⟩

/-- The original low count is exactly the certified inner rectangle plus the
unpaid physical boundary. The coefficient 400 is retained on both terms. -/
theorem original_low_partition (N : ℕ) (ε : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ)) :
    (∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ))).card : ℝ)) =
      (400 * ∑ p ∈ rectangle N ε M T, goldbachG12NormalizedCoefficient N p.1 *
        (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
      (400 * ∑ p ∈ boundary N ε M T, goldbachG12NormalizedCoefficient N p.1 *
        (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) := by
  rw [← original_low_count]
  exact weighted_partition N ε M T hlow hhigh _

end G12LowRectangle
