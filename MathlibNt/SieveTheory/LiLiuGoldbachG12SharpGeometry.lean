import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpWeight
import MathlibNt.SieveTheory.LiLiuGoldbachAuthorCrossIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegralBridge

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original low first-prime box leaves at least 3.16 q-logarithms. -/
theorem g12Sharp_low_log_budget (L R Q S T : ℝ) (hL : 0 ≤ L)
    (hR : R ≤ L / 10) (hQ : Q ≤ (4 / 33 : ℝ) * L)
    (hS : S ≤ (4 / 33 : ℝ) * L) (hT : T ≤ (3 / 11 : ℝ) * L) :
    (79 / 25 : ℝ) * Q ≤ L - (R + Q + S + T) := by
  linarith

/-- Low first-prime geometry for the literal original closed cross. -/
theorem g12Sharp_canonical_low_logQuotient
    {N r q s t : ℕ} (hN : 4 ≤ N)
    (ht : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)))
    (hs : s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)))
    (hr : r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ))
    (hq : q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ))
    (hcut : (r : ℝ) < (N : ℝ)^(1/10 : ℝ)) :
    (79/25 : ℝ) ≤ Real.log ((N : ℝ)/(r*q*s*t : ℕ)) / Real.log (q : ℝ) := by
  have ht' := mem_goldbachClosedPrimes_iff.mp ht
  have hs' := mem_goldbachClosedPrimes_iff.mp hs
  have hr' := mem_goldbachClosedPrimes_iff.mp hr
  have hq' := mem_goldbachClosedPrimes_iff.mp hq
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr'.1.pos
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq'.1.pos
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs'.1.pos
  have htp : (0 : ℝ) < t := by exact_mod_cast ht'.1.pos
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hR := Real.log_le_log hrp hcut.le
  have hQ := Real.log_le_log hqp (hq'.2.2.2.trans hs'.2.2.2)
  have hS := Real.log_le_log hsp hs'.2.2.2
  have hT := Real.log_le_log htp ht'.2.2.2
  rw [Real.log_rpow hNp] at hR hQ hS hT
  have hb := g12Sharp_low_log_budget (Real.log (N : ℝ)) (Real.log (r : ℝ))
    (Real.log (q : ℝ)) (Real.log (s : ℝ)) (Real.log (t : ℝ)) hL
    (by linarith) hQ hS hT
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq'.1.one_lt)
  apply (le_div_iff₀ hlogq).mpr
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Real.log_div hNp.ne' (by positivity),
    Real.log_mul (by positivity : (r : ℝ)*q*s ≠ 0) htp.ne',
    Real.log_mul (by positivity : (r : ℝ)*q ≠ 0) hsp.ne',
    Real.log_mul hrp.ne' hqp.ne']
  exact hb

/-- The logarithmic step cutoff is exactly the physical low cutoff. -/
theorem g12Sharp_low_cut_of_log {N r : ℕ} (hN : 4 ≤ N) (hr : r.Prime)
    (h : Real.log (r : ℝ)/Real.log (N : ℝ) < (1/10 : ℝ)) :
    (r : ℝ) < (N : ℝ)^(1/10 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hl := (div_lt_iff₀ hlogN).mp h
  have he : Real.log ((N : ℝ)^(1/10 : ℝ)) = (1/10 : ℝ)*Real.log (N : ℝ) :=
    Real.log_rpow hNp _
  apply (Real.log_lt_log_iff (by exact_mod_cast hr.pos) (Real.rpow_pos_of_pos hNp _)).mp
  rwa [he]

/-- The actual Buchstab value is bounded by the step factor, not a uniform constant. -/
theorem g12Sharp_buchstab_le_factor {N : ℕ} (hN : 4 ≤ N)
    {v : GoldbachG11Label}
    (hv : v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))) :
    LiLiuPrereqBuchstab.buchstab
      (Real.log ((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ)) ≤
      G12SharpWeight.factor (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ)) := by
  rcases v with ⟨t,s,r,q⟩
  have hm : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG12Labels, Finset.mem_sigma] using hv
  unfold G12SharpWeight.factor
  split_ifs with hc
  · have hcut := g12Sharp_low_cut_of_log hN (mem_goldbachClosedPrimes_iff.mp hm.2.2.1).1 hc
    have hb := LiLiuGoldbachG12BuchstabMajorant.buchstab_le_561990
      (g12Sharp_canonical_low_logQuotient hN hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 hcut)
    exact hb.trans (by norm_num)
  · exact LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383
      (goldbachG12_canonical_logQuotient_bounds (by omega) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2).1

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
