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


def beta (N r : ℕ) : ℝ := if r.Coprime N then primeSWBeta r else 0

/-- Exact signed finite discrepancy; no absolute value is taken inside either sum. -/
def discrepancy (N : ℕ) (S : Finset (ℕ × ℕ)) (Q : Finset ℕ)
    (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ reducedModuli Q (N : ℤ), c d *
    ((∑ p ∈ S, if Int.ModEq d ((p.1 : ℤ)*p.2) (N : ℤ)
        then goldbachG12NormalizedCoefficient N p.1 else 0) -
      (∑ p ∈ S, if (p.1*p.2).Coprime d
        then goldbachG12NormalizedCoefficient N p.1 else 0) / (d.totient : ℝ))


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


end G12LowRectangle
