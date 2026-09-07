import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutputWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMass

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace G12ClippedWindow

/-- The coefficient and endpoints are common to every modulus. -/
def Admissible (N : ℕ) (ε : ℝ) (g L U : ℕ → ℝ) : Prop :=
  ∀ m ∈ goldbachG12ActiveProductSupport N,
    (0 ≤ g m ∧ g m ≤ goldbachG12NormalizedCoefficient N m) ∧
    goldbachG11PiLiLo N ε m ≤ L m ∧ L m ≤ U m ∧ U m ≤ goldbachG11PiLiHi N m

/-- Literal prime Ioc, with the original finite ambient carrier. -/
def window (N : ℕ) (L U : ℕ → ℝ) (m : ℕ) : Finset ℕ :=
  (range (N+1)).filter fun r => r.Prime ∧ L m < r ∧ (r : ℝ) ≤ U m

variable {N : ℕ} {ε : ℝ} {g L U : ℕ → ℝ}

theorem window_subset (h : Admissible N ε g L U) {m : ℕ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    window N L U m ⊆ goldbachG11LinkedPrimeWindow N ε m := by
  intro r hr
  obtain ⟨hr,hp,hl,hu⟩ := mem_filter.mp hr
  exact mem_filter.mpr ⟨hr,hp,(h m hm).2.1.trans_lt hl,hu.trans (h m hm).2.2.2⟩

theorem endpoint_nonneg (hN : 2 ≤ N) (h : Admissible N ε g L U)
    {m : ℕ} (hm : m ∈ goldbachG12ActiveProductSupport N) :
    0 ≤ L m ∧ 0 ≤ U m := by
  have hl := ((Real.rpow_nonneg (Nat.cast_nonneg N) _).trans
    (goldbachG12PiLiEndpoints_bounds hN hm).1).trans (h m hm).2.1
  exact ⟨hl, hl.trans (h m hm).2.2.1⟩

theorem apWindow_eq_sdiff {m : ℕ} (h : Admissible N ε g L U) (d b : ℕ)
    (hN : 2 ≤ N) (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (window N L U m).filter (fun r => Nat.ModEq d (m*r) b) =
      scaledPrimeSet ((m : ℝ)*U m) d b m \
        scaledPrimeSet ((m : ℝ)*L m) d b m := by
  have hm0 := (goldbachG12ActiveProductSupport_data hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hhiN := (h m hm).2.2.2.trans (goldbachG12PiLiEndpoints_bounds (ε := ε) hN hm).2.2
  have hlo0 := (endpoint_nonneg hN h hm).1
  have hhi0 := (endpoint_nonneg hN h hm).2
  apply Finset.ext
  intro r
  simp only [window, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff,
    mem_scaledPrimeSet (mul_nonneg hmR.le hhi0) hm0,
    mem_scaledPrimeSet (mul_nonneg hmR.le hlo0) hm0]
  constructor
  · rintro ⟨⟨_, hp, hl, hh⟩, hc⟩
    refine ⟨⟨hp, mul_le_mul_of_nonneg_left hh hmR.le, hc⟩, ?_⟩
    rintro ⟨_, hbad, _⟩
    have := mul_lt_mul_of_pos_left hl hmR
    linarith
  · rintro ⟨⟨hp, hh, hc⟩, hnlo⟩
    have hlprod : (m : ℝ)*L m < (m : ℝ)*r := by
      by_contra h
      exact hnlo ⟨hp, le_of_not_gt h, hc⟩
    have hl : L m < (r : ℝ) := by nlinarith
    have hhr : (r : ℝ) ≤ U m := by nlinarith
    have hrm : (r : ℝ)*(m : ℝ) ≤ N := (le_div_iff₀ hmR).mp (hhr.trans hhiN)
    have hrmN : r*m ≤ N := by exact_mod_cast hrm
    have hrN : r ≤ N := by
      nlinarith [Nat.mul_le_mul_left r (show 1 ≤ m by omega)]
    exact ⟨⟨Nat.lt_succ_of_le hrN, hp, hl, hhr⟩, hc⟩

/-- Actual AP cardinality: the high window has the unchanged inverse residue. -/
theorem apWindow_card_eq_inverse {m : ℕ} (h : Admissible N ε g L U) (d b : ℕ)
    (hN : 2 ≤ N) (hm : m ∈ goldbachG12ActiveProductSupport N) (hmd : m.Coprime d) :
    (((window N L U m).filter (fun r => Nat.ModEq d (m*r) b)).card : ℝ) =
      (primesInAP ⌊U m⌋₊ d (natInvMod d m*b % d) : ℝ) -
        primesInAP ⌊L m⌋₊ d (natInvMod d m*b % d) := by
  have hm0 := (goldbachG12ActiveProductSupport_data hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hlo0 := (endpoint_nonneg hN h hm).1
  have hlh := (h m hm).2.2.1
  have hhi0 := hlo0.trans hlh
  have hsub : scaledPrimeSet ((m : ℝ)*L m) d b m ⊆
      scaledPrimeSet ((m : ℝ)*U m) d b m := by
    intro r hr
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hlo0) hm0] at hr
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hhi0) hm0]
    exact ⟨hr.1, hr.2.1.trans (mul_le_mul_of_nonneg_left hlh hmR.le), hr.2.2⟩
  rw [apWindow_eq_sdiff h d b hN hm,
    Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  change (scaledPrimeCount _ d b m : ℝ) - scaledPrimeCount _ d b m = _
  rw [scaledPrimeCount_eq_inverse _ d b m (mul_nonneg hmR.le hhi0) hm0 hmd,
    scaledPrimeCount_eq_inverse _ d b m (mul_nonneg hmR.le hlo0) hm0 hmd]
  simp only [mul_div_cancel_left₀ _ (ne_of_gt hmR)]

theorem window_card (hN : 2 ≤ N) (h : Admissible N ε g L U)
    {m : ℕ} (hm : m ∈ goldbachG12ActiveProductSupport N) :
    ((window N L U m).card : ℝ) =
      PanPrincipal.primeCount ⌊U m⌋₊ - PanPrincipal.primeCount ⌊L m⌋₊ := by
  have hp (t : ℕ) : (primesInAP t 1 0 : ℝ) = PanPrincipal.primeCount t := by
    simp [primesInAP, PanPrincipal.primeCount, Nat.ModEq, Nat.mod_one, Finset.sum_boole]
  have ha := apWindow_card_eq_inverse h 1 0 hN hm (Nat.coprime_one_right m)
  simpa only [Nat.mod_one, hp, Nat.modEq_one, filter_true_of_mem (fun _ _ => True.intro)] using ha

end G12ClippedWindow
