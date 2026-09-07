import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutput

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve

namespace G12LowHighOutput

/-- A closed real high cut is an open cut at the preceding natural number. -/
def highCut (N : ℕ) : ℝ := ((⌈(N : ℝ)^(1/10 : ℝ)⌉₊ - 1 : ℕ) : ℝ)

def highLo (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  min (goldbachG11PiLiHi N m) (max (goldbachG11PiLiLo N ε m) (highCut N))

def highWindow (N : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  (goldbachG11LinkedPrimeWindow N ε m).filter fun r => (N : ℝ)^(1/10 : ℝ) ≤ r

theorem highCut_lt_iff (N r : ℕ) (hr : 0 < r) :
    highCut N < r ↔ (N : ℝ)^(1/10 : ℝ) ≤ r := by
  unfold highCut
  rw [Nat.cast_lt]
  have h : ⌈(N : ℝ)^(1/10 : ℝ)⌉₊ ≤ r ↔ (N : ℝ)^(1/10 : ℝ) ≤ r := Nat.ceil_le
  rw [← h]
  omega

theorem highLo_bounds {N m : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    goldbachG11PiLiLo N ε m ≤ highLo N ε m ∧ highLo N ε m ≤ goldbachG11PiLiHi N m := by
  exact ⟨le_min (goldbachG12PiLiEndpoints_bounds hN hm).2.1 (le_max_left _ _),
    min_le_left _ _⟩

/-- Literal closed-high prime window, not an arbitrary filtered SW assertion. -/
theorem mem_highWindow (N m r : ℕ) (ε : ℝ) :
    r ∈ highWindow N ε m ↔ r ∈ range (N+1) ∧ r.Prime ∧
      highLo N ε m < r ∧ (r : ℝ) ≤ goldbachG11PiLiHi N m := by
  simp only [highWindow, goldbachG11LinkedPrimeWindow, mem_filter]
  constructor
  · rintro ⟨⟨hr,hp,hlo,hhi⟩,ha⟩
    exact ⟨hr,hp,(min_le_right _ _).trans_lt
      (max_lt hlo ((highCut_lt_iff N r hp.pos).mpr ha)),hhi⟩
  · rintro ⟨hr,hp,hlo,hhi⟩
    have hmax : max (goldbachG11PiLiLo N ε m) (highCut N) < r := by
      rcases min_lt_iff.mp hlo with hbad | hgood
      · exact False.elim ((not_lt_of_ge hhi) hbad)
      · exact hgood
    exact ⟨⟨hr,hp,(max_lt_iff.mp hmax).1,hhi⟩,
      (highCut_lt_iff N r hp.pos).mp (max_lt_iff.mp hmax).2⟩

/-- Exact AP identity at the same modulus and product residue. -/
theorem highAPWindow_eq_sdiff {N m : ℕ} {ε : ℝ} (d b : ℕ)
    (hN : 2 ≤ N) (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (highWindow N ε m).filter (fun r => Nat.ModEq d (m*r) b) =
      scaledPrimeSet ((m : ℝ)*goldbachG11PiLiHi N m) d b m \
        scaledPrimeSet ((m : ℝ)*highLo N ε m) d b m := by
  have hm0 := (goldbachG12ActiveProductSupport_data hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨hzlo, hlh, hhiN⟩ := goldbachG12PiLiEndpoints_bounds (ε := ε) hN hm
  have hlo0 : 0 ≤ highLo N ε m :=
    ((Real.rpow_nonneg (Nat.cast_nonneg N) _).trans hzlo).trans (highLo_bounds hN hm).1
  have hhi0 := hlo0.trans (highLo_bounds hN hm).2
  apply Finset.ext
  intro r
  simp only [Finset.mem_filter, mem_highWindow, Finset.mem_range, Finset.mem_sdiff,
    mem_scaledPrimeSet (mul_nonneg hmR.le hhi0) hm0,
    mem_scaledPrimeSet (mul_nonneg hmR.le hlo0) hm0]
  constructor
  · rintro ⟨⟨_, hp, hl, hh⟩, hc⟩
    refine ⟨⟨hp, mul_le_mul_of_nonneg_left hh hmR.le, hc⟩, ?_⟩
    rintro ⟨_, hbad, _⟩
    have := mul_lt_mul_of_pos_left hl hmR
    linarith
  · rintro ⟨⟨hp, hh, hc⟩, hnlo⟩
    have hlprod : (m : ℝ)*highLo N ε m < (m : ℝ)*r := by
      by_contra h
      exact hnlo ⟨hp, le_of_not_gt h, hc⟩
    have hl : highLo N ε m < (r : ℝ) := by nlinarith
    have hhr : (r : ℝ) ≤ goldbachG11PiLiHi N m := by nlinarith
    have hrm : (r : ℝ)*(m : ℝ) ≤ N := (le_div_iff₀ hmR).mp (hhr.trans hhiN)
    have hrmN : r*m ≤ N := by exact_mod_cast hrm
    have hrN : r ≤ N := by
      nlinarith [Nat.mul_le_mul_left r (show 1 ≤ m by omega)]
    exact ⟨⟨Nat.lt_succ_of_le hrN, hp, hl, hhr⟩, hc⟩

/-- Actual AP cardinality: the high window has the unchanged inverse residue. -/
theorem highAPWindow_card_eq_inverse {N m : ℕ} {ε : ℝ} (d b : ℕ)
    (hN : 2 ≤ N) (hm : m ∈ goldbachG12ActiveProductSupport N) (hmd : m.Coprime d) :
    (((highWindow N ε m).filter (fun r => Nat.ModEq d (m*r) b)).card : ℝ) =
      (primesInAP ⌊goldbachG11PiLiHi N m⌋₊ d (natInvMod d m*b % d) : ℝ) -
        primesInAP ⌊highLo N ε m⌋₊ d (natInvMod d m*b % d) := by
  have hm0 := (goldbachG12ActiveProductSupport_data hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hlo0 : 0 ≤ highLo N ε m :=
    ((Real.rpow_nonneg (Nat.cast_nonneg N) _).trans
      (goldbachG12PiLiEndpoints_bounds hN hm).1).trans (highLo_bounds hN hm).1
  have hlh := (highLo_bounds (ε := ε) hN hm).2
  have hhi0 := hlo0.trans hlh
  have hsub : scaledPrimeSet ((m : ℝ)*highLo N ε m) d b m ⊆
      scaledPrimeSet ((m : ℝ)*goldbachG11PiLiHi N m) d b m := by
    intro r hr
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hlo0) hm0] at hr
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hhi0) hm0]
    exact ⟨hr.1, hr.2.1.trans (mul_le_mul_of_nonneg_left hlh hmR.le), hr.2.2⟩
  rw [highAPWindow_eq_sdiff d b hN hm,
    Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  change (scaledPrimeCount _ d b m : ℝ) - scaledPrimeCount _ d b m = _
  rw [scaledPrimeCount_eq_inverse _ d b m (mul_nonneg hmR.le hhi0) hm0 hmd,
    scaledPrimeCount_eq_inverse _ d b m (mul_nonneg hmR.le hlo0) hm0 hmd]
  simp only [mul_div_cancel_left₀ _ (ne_of_gt hmR)]

/-- The AP test is literally divisibility of the original output. -/
theorem highAPWindow_eq_output_dvd {N m : ℕ} {ε : ℝ} (d : ℕ)
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (highWindow N ε m).filter (fun r => Nat.ModEq d (m*r) N) =
      (highWindow N ε m).filter (fun r => d ∣ N-r*m) := by
  apply Finset.ext
  intro r
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hr
  rw [Nat.mul_comm m r, Nat.modEq_iff_dvd'
    (goldbachG12LinkedPrimeWindow_product_le hm (Finset.mem_filter.mp hr).1)]

/-- The high original output fibres use this very window, with their original
coprimality gate and primality test retained. -/
theorem high_original_fiber {N m : ℕ} (ε : ℝ)
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
      (fun r : ℕ => (N : ℝ)^(1/10 : ℝ) ≤ (r : ℝ)) =
    (highWindow N ε m).filter (fun r => ¬r ∣ N ∧ (N-r*m).Prime) := by
  rw [goldbachG12ProductFirstPrimeFiber_eq_linkedWindow hm]
  apply Finset.ext
  intro r
  simp only [highWindow, Finset.mem_filter]
  tauto

end G12LowHighOutput
