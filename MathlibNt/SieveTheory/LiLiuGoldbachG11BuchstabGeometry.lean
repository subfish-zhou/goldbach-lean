import MathlibNt.SieveTheory.LiLiuGoldbachWeightQuadruple

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
    Real.log (p : ℝ) / Real.log (N : ℝ) ∈ Icc (4 / 53 : ℝ) (4 / 33) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hlo
  have hh := Real.log_le_log hpp hhi
  rw [Real.log_rpow hNp] at hl hh
  exact ⟨(le_div_iff₀ hlogN).mpr hl, (div_le_iff₀ hlogN).mpr hh⟩

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
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr'.1.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq'.1.ne_zero
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs'.1.ne_zero
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht'.1.ne_zero
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos
    (by exact_mod_cast (show 1 < N by omega))).ne'
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos
    (by exact_mod_cast hq'.1.one_lt)).ne'
  have hprod : ((r * q * s * t : ℕ) : ℝ) ≠ 0 := by
    simpa only [Nat.cast_mul] using mul_ne_zero (mul_ne_zero (mul_ne_zero hr0 hq0) hs0) ht0
  have hlogs : Real.log ((r * q * s * t : ℕ) : ℝ) =
      Real.log (r : ℝ) + Real.log (q : ℝ) + Real.log (s : ℝ) + Real.log (t : ℝ) := by
    simp only [Nat.cast_mul]
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hr0 hq0) hs0) ht0,
      Real.log_mul (mul_ne_zero hr0 hq0) hs0, Real.log_mul hr0 hq0]
  have heq : Real.log ((N : ℝ) / (r * q * s * t : ℕ)) / Real.log (q : ℝ) =
      (1 - Real.log (r : ℝ) / Real.log (N : ℝ) -
        Real.log (q : ℝ) / Real.log (N : ℝ) -
        Real.log (s : ℝ) / Real.log (N : ℝ) -
        Real.log (t : ℝ) / Real.log (N : ℝ)) /
        (Real.log (q : ℝ) / Real.log (N : ℝ)) := by
    rw [Real.log_div hN0 hprod, hlogs]
    field_simp
    ring
  rw [heq]
  exact hbound

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig