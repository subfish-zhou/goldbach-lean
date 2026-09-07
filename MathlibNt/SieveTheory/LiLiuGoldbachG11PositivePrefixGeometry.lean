import MathlibNt.SieveTheory.LiLiuGoldbachG11BuchstabGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughQuotient

open Set
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Both strict cofactor endpoints come from the actual prime-output pair, not from a
zero-prefix enlargement. This finite statement even allows an arbitrary real epsilon. -/
theorem goldbachG11RoughPairs_cofactor_window
    {N p m : ℕ} {ε z b : ℝ} {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N z b)
    (hpm : (p, m) ∈ goldbachG11RoughPairs N ε v) :
    ε * (N : ℝ) / (goldbachG11LabelProd v : ℝ) < (m : ℝ) ∧
      (m : ℝ) < (N : ℝ) / (goldbachG11LabelProd v : ℝ) := by
  rcases mem_goldbachG11RoughPairs_iff.mp hpm with ⟨_, _, _, hp, hcut, heq, _⟩
  have hd : (0 : ℝ) < goldbachG11LabelProd v := by
    exact_mod_cast goldbachG11LabelProd_pos hv
  have heqR : (p : ℝ) + (goldbachG11LabelProd v : ℝ) * (m : ℝ) = N := by
    exact_mod_cast heq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · apply (div_lt_iff₀ hd).mpr
    nlinarith
  · apply (lt_div_iff₀ hd).mpr
    nlinarith

/-- A fixed positive prefix has a uniform Buchstab parameter window. The threshold precedes
all four varying prime labels; this does not assert a rough-number asymptotic. -/
theorem goldbachG11_positivePrefix_logQuotient_bounds
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
        Real.log (ε * (N : ℝ) / (goldbachG11LabelProd v : ℝ)) /
          Real.log (v.2.2.2 : ℝ) ∈ Icc (4 : ℝ) (37 / 4) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (Real.exp (53 * |Real.log ε|)) (4 : ℝ))
  have h40 : 4 ≤ N₀ := by
    have hh : (4 : ℝ) ≤ N₀ := (le_max_right _ _).trans hN₀.le
    exact_mod_cast hh
  refine ⟨N₀, h40, ?_⟩
  intro N hNN v hv
  have hN4 : 4 ≤ N := h40.trans hNN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heN : Real.exp (53 * |Real.log ε|) ≤ (N : ℝ) :=
    ((le_max_left _ _).trans hN₀.le).trans (by exact_mod_cast hNN)
  have hLN := Real.log_le_log (Real.exp_pos _) heN
  rw [Real.log_exp] at hLN
  have hprod := goldbachG11LabelProd_pos hv
  rcases v with ⟨t, s, r, q⟩
  change 0 < r * q * s * t at hprod
  have hprodR : (0 : ℝ) < ((r * q * s * t : ℕ) : ℝ) := by exact_mod_cast hprod
  have hmem : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ))
        ((N : ℝ)^(4 / 33 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (t : ℝ) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG11Labels, Finset.mem_sigma] using hv
  rcases hmem with ⟨ht, hs, hr, hq⟩
  have hr' := mem_goldbachClosedPrimes_iff.mp hr
  have hq' := mem_goldbachClosedPrimes_iff.mp hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq'.1.one_lt)
  have hqL := Real.log_le_log (Real.rpow_pos_of_pos hNp (4 / 53 : ℝ))
    (hr'.2.2.1.trans hq'.2.2.1)
  rw [Real.log_rpow hNp] at hqL
  have hshiftL : -(1 / 4 : ℝ) ≤ Real.log ε / Real.log (q : ℝ) := by
    apply (le_div_iff₀ hlogq).mpr
    nlinarith [neg_abs_le (Real.log ε)]
  have hshiftU : Real.log ε / Real.log (q : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hε.le hε1) hlogq.le
  have hb := goldbachG11_canonical_logQuotient_bounds (by omega : 2 ≤ N) ht hs hr hq
  change Real.log (ε * (N : ℝ) / ((r * q * s * t : ℕ) : ℝ)) /
      Real.log (q : ℝ) ∈ Icc (4 : ℝ) (37 / 4)
  rw [mul_div_assoc, Real.log_mul hε.ne' (div_ne_zero hNp.ne' hprodR.ne'), add_div]
  constructor
  · linarith [hb.1]
  · linarith [hb.2]

/-- Every actual cofactor lies strictly inside the common parameter window, after a
threshold depending only on epsilon and not on its prime label or output prime. -/
theorem goldbachG11_actualRoughCofactor_log_bounds
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
      ∀ pm ∈ goldbachG11RoughPairs N ε v,
        Real.log (pm.2 : ℝ) / Real.log (v.2.2.2 : ℝ) ∈ Ioo (4 : ℝ) (37 / 4) := by
  obtain ⟨N₀, hN₀, hlow⟩ := goldbachG11_positivePrefix_logQuotient_bounds ε hε hε1
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN v hv pm hpm
  rcases pm with ⟨p, m⟩
  have hw := goldbachG11RoughPairs_cofactor_window hv hpm
  have hlower := hlow N hNN v hv
  have hprod := goldbachG11LabelProd_pos hv
  have hm1 := (mem_goldbachG11RoughPairs_iff.mp hpm).2.1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rcases v with ⟨t, s, r, q⟩
  have hqprime := (mem_goldbachG11Labels_iff.mp hv).2.1
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hqprime.one_lt)
  have hmem : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ))
        ((N : ℝ)^(4 / 33 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (t : ℝ) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG11Labels, Finset.mem_sigma] using hv
  rcases hmem with ⟨ht, hs, hr, hq⟩
  have hupper := goldbachG11_canonical_logQuotient_bounds (by omega : 2 ≤ N) ht hs hr hq
  have hdR : (0 : ℝ) < (goldbachG11LabelProd ⟨t, s, r, q⟩ : ℝ) := by
    exact_mod_cast hprod
  have hlo := div_lt_div_of_pos_right
    (Real.log_lt_log (div_pos (mul_pos hε hNp) hdR) hw.1) hlogq
  have hhi := div_lt_div_of_pos_right (Real.log_lt_log hmR hw.2) hlogq
  exact ⟨hlower.1.trans_lt hlo, hhi.trans_le hupper.2⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig