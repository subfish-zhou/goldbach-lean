module

public import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabGeometry

@[expose] public section

open Set
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A domain estimate for the literal Buchstab argument; no estimate for the Buchstab function. -/
theorem goldbachG11_buchstabParameter_bounds {u v w x : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (4 / 33))
    (hv : v ∈ Icc (4 / 53 : ℝ) (4 / 33))
    (hw : w ∈ Icc (4 / 53 : ℝ) (4 / 33))
    (hx : x ∈ Icc (4 / 53 : ℝ) (4 / 33)) :
    (1 - u - v - w - x) / v ∈ Icc (17 / 4 : ℝ) (37 / 4) := by
  have hv0 : 0 < v := by linarith [hv.1]
  constructor
  · apply (le_div_iff₀ hv0).mpr
    linarith [hu.2, hv.2, hw.2, hx.2]
  · apply (div_le_iff₀ hv0).mpr
    linarith [hu.1, hv.1, hw.1, hx.1]

theorem goldbachG11_logPrimeExponent_mem {N p : ℕ} (hN : 2 ≤ N)
    (hp : p.Prime)
    (hlo : (N : ℝ)^(4 / 53 : ℝ) ≤ p)
    (hhi : (p : ℝ) ≤ (N : ℝ)^(4 / 33 : ℝ)) :
    Real.log (p : ℝ) / Real.log (N : ℝ) ∈ Icc (4 / 53 : ℝ) (4 / 33) :=
  goldbachG12_logPrimeExponent_mem hN hp hlo hhi

/-- Actual closed G11 labels give the same compact Buchstab window, including repeated primes. -/
theorem goldbachG11_canonical_logQuotient_bounds
    {N r q s t : ℕ} (hN : 2 ≤ N)
    (ht : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)))
    (hs : s ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (t : ℝ))
    (hr : r ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (s : ℝ))
    (hq : q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ)) :
    Real.log ((N : ℝ) / (r * q * s * t : ℕ)) / Real.log (q : ℝ) ∈
      Icc (17 / 4 : ℝ) (37 / 4) := by
  have ht' := mem_goldbachClosedPrimes_iff.mp ht
  have hs' := mem_goldbachClosedPrimes_iff.mp hs
  have hr' := mem_goldbachClosedPrimes_iff.mp hr
  have hq' := mem_goldbachClosedPrimes_iff.mp hq
  have hsb := hs'.2.2.2.trans ht'.2.2.2
  have hru := goldbachG11_logPrimeExponent_mem hN hr'.1 hr'.2.2.1
    (hr'.2.2.2.trans hsb)
  have hqu := goldbachG11_logPrimeExponent_mem hN hq'.1
    (hr'.2.2.1.trans hq'.2.2.1) (hq'.2.2.2.trans hsb)
  have hsu := goldbachG11_logPrimeExponent_mem hN hs'.1 hs'.2.2.1 hsb
  have htu := goldbachG11_logPrimeExponent_mem hN ht'.1 ht'.2.2.1 ht'.2.2.2
  have hbound := goldbachG11_buchstabParameter_bounds hru hqu hsu htu
  rw [log_fourPrimeQuotient_div_log hN hr'.1 hq'.1 hs'.1 ht'.1]
  exact hbound

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
