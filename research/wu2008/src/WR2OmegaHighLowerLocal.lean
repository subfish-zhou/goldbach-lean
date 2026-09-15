import WR2OmegaHighUpper

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighBoxRecovery HighO2Terminal
open Finset Real Filter
open scoped Classical Topology Interval BigOperators
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem outer_support {N p : ℕ} {δ : ℝ} (j : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes (index j) N) :
    0 < p ∧ p ≤ N ∧ (N : ℝ) ^ (10 * highEta) ≤ (N : ℝ) ^ (1 / 2 - δ) / p ∧
      1 < (N : ℝ) ^ (1 / 2 - δ) / p := by
  have hg := support_geometry (N := N) j hN hh
  have hsp : p ∈ boxConvolutionSupport (windows j N) := (support j N).symm ▸ hp
  have hf := HighO3.phi_bounds hN (mem_primeWindow.mp hp).1.pos hd
    (show δ < 1 / 2 by linarith) (show 0 < highEta by norm_num [highEta]) (hg.2 p hsp)
  refine ⟨(mem_primeWindow.mp hp).1.pos, ?_, hf.1, hf.2.1⟩
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h := (prime_geometry j hN hp).2.2.2.trans
    (rpow_le_rpow_of_exponent_le hn (by norm_num [highEta] : 1 / 2 - 100 * highEta ≤ (1 : ℝ)))
  rw [rpow_one] at h
  exact_mod_cast h

theorem inner_geometry {N p q : ℕ} {δ : ℝ} (j : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes (index j) N)
    (hq : q ∈ primeWindow N (wuLocalCutoff N δ p (psiTop (index j)))
      (wuLocalCutoff N δ p (psiNode (index j)))) :
    (N : ℝ) ^ highEta ≤ q ∧ (q : ℝ) ≤ N ∧
      ((p * q : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ - 10 * highEta) := by
  have hs := outer_support j hN hd hh hp
  have hg := geometry j
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hs.1
  have hr0 : 0 < (N : ℝ) ^ (1 / 2 - δ) / p := by linarith [hs.2.2.2]
  have hqm := mem_primeWindow.mp hq
  have hhalf : (q : ℝ) ≤ ((N : ℝ) ^ (1 / 2 - δ) / p) ^ (1 / 2 : ℝ) :=
    hqm.2.2.2.le.trans (rpow_le_rpow_of_exponent_le hs.2.2.2.le
      (one_div_le_one_div_of_le (by norm_num) hg.1))
  have hpq : ((p * q : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ - 10 * highEta) := by
    have hpow : (N : ℝ) ^ (1 / 2 - δ) * p ≤
        ((N : ℝ) ^ (1 / 2 - δ - 10 * highEta)) ^ 2 := by
      calc
        _ ≤ (N : ℝ) ^ (1 / 2 - δ) * (N : ℝ) ^ (1 / 2 - 100 * highEta) :=
          mul_le_mul_of_nonneg_left (prime_geometry j hN hp).2.2.2 (by positivity)
        _ = (N : ℝ) ^ ((1 / 2 - δ) + (1 / 2 - 100 * highEta)) := (rpow_add hn0 _ _).symm
        _ ≤ (N : ℝ) ^ ((1 / 2 - δ - 10 * highEta) * 2) :=
          rpow_le_rpow_of_exponent_le hn.le (by norm_num [highEta]; linarith)
        _ = _ := by rw [rpow_mul (Nat.cast_nonneg N), rpow_two]
    have hsq : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 2 - δ) / p := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg q) hhalf 2
      have heq : (((N : ℝ) ^ (1 / 2 - δ) / p) ^ (1 / 2 : ℝ)) ^ 2 =
          (N : ℝ) ^ (1 / 2 - δ) / p := by
        rw [← rpow_two, ← rpow_mul hr0.le]; norm_num
      rwa [heq] at h
    have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hp0).mp hsq) hp0.le
    rw [Nat.cast_mul]
    nlinarith [rpow_nonneg (Nat.cast_nonneg N) (1 / 2 - δ - 10 * highEta)]
  refine ⟨?_, ?_, hpq⟩
  · have hw := support_geometry (N := N) j hN hh
    exact (cutoff_lower hN hs.1 (show 0 < highEta by norm_num [highEta])
      (by linarith [hg.2.2.1]) (by linarith [hg.2.2.2.1])
      (hw.2 p ((support j N).symm ▸ hp))).trans hqm.2.2.1
  · have hqN := hqm.2.2.2.le.trans (seven_cutoff_geometry (index j) hN hd hh hp).2.2.1
    apply hqN.trans
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hn.le
      (show truncatedSixthLowerAlpha ≤ 1 by norm_num [truncatedSixthLowerAlpha])

theorem theta_sum (j : Fin 4) (N : ℕ) (δ : ℝ) :
    theta j N δ = ∑ p ∈ psiPrimes (index j) N, HighSix.thetaAtom N δ p := by
  unfold theta boxTheta HighSix.thetaAtom HighSix.R
  rw [mul_sum]
  simpa only [mul_div_assoc, mul_left_comm] using
    weighted_sum j N (fun p => 4 * logarithmicIntegral N * wuSingularSeries (p * N) /
      ((Nat.totient p : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / p)))

theorem theta_atom_nonneg {N p : ℕ} {δ : ℝ} (j : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes (index j) N) : 0 ≤ HighSix.thetaAtom N δ p := by
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN)
  have hC := wuSingularSeries_pos (p * N)
    (Nat.mul_pos (mem_primeWindow.mp hp).1.pos (show 0 < N by omega))
  have hl := log_pos (outer_support j hN hd hh hp).2.2.2
  unfold HighSix.thetaAtom HighSix.R
  positivity

theorem actual_atom_lower {δ e : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (he : 0 < e) (he1 : e ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      ∀ p ∈ psiPrimes (index j) N,
      ∀ q ∈ primeWindow (p * N) (wuLocalCutoff N δ p (psiTop (index j)))
        (wuLocalCutoff N δ p (psiNode (index j))),
      HighSix.thetaAtom N δ p *
        (logCoefficient e (ratio N p q δ (psiTop (index j))) /
          (((q : ℝ) - 2) * (1 - log (q : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / p)))) -
        apAtom N (convolutionModulusCutoff N δ) (p * q) ≤
      (sourceSieveCount N (p * q) (p * N) (wuLocalCutoff N δ p (psiTop (index j))) : ℝ) := by
  obtain ⟨T0, hT04, hl⟩ := local_count_lower hd.le he he1
  obtain ⟨T1, hlarge⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < highEta by norm_num [highEta])).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j p hp q hq
  have hN4 : 4 ≤ N := hT04.trans (by omega)
  have hqm := mem_primeWindow.mp hq
  have hqN := selected_subset_original N p _ _ hq
  have hg := inner_geometry j (show 2 ≤ N by omega) hd hh hp hqN
  have hsp := outer_support j (show 2 ≤ N by omega) hd hh hp
  have hpar := geometry j
  have hu := ratio_domain hsp.2.2.2 hpar.1 hpar.2.2.1 hpar.2.2.2.1
    hpar.2.2.2.2.2.1 hqN
  have h := hl N (by omega) hEven (p * q) (Nat.mul_pos hsp.1 hqm.1.pos)
    hg.2.2 (ratio N p q δ (psiTop (index j))) hu.1 hu.2
  rw [ratio_cutoff hsp.2.2.2 hqm.1.pos (by linarith [hpar.2.2.1])
      (by linarith [hu.1]),
    omega2_source_count_prime_modulus_eq N p hqm.1 hqm.2.2.1] at h
  have hq4 : (4 : ℝ) ≤ q := (hlarge N (by omega)).trans hg.1
  have hqd : ¬q ∣ p := hqm.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp hqm.2.1).1
  have hw := wu_inserted_theta_weight (show 0 < N by omega) hsp.1 hqm.1
    (show 2 < q by exact_mod_cast (show (2 : ℝ) < q by linarith))
    (Nat.coprime_mul_iff_right.mp hqm.2.1).2 hsp.2.2.2
  simp only [if_neg hqd] at hw
  rw [Nat.cast_mul, hw] at h
  convert h using 1
  dsimp [HighSix.thetaAtom, HighSix.R, logCoefficient]
  rw [max_eq_right hu.1]
  simp only [div_mul_eq_div_div]
  ring

#check @WuPaper.R2OmegaHigh.outer_support
#check @WuPaper.R2OmegaHigh.inner_geometry
#check @WuPaper.R2OmegaHigh.theta_sum
#check @WuPaper.R2OmegaHigh.theta_atom_nonneg
#check @WuPaper.R2OmegaHigh.actual_atom_lower
#print axioms WuPaper.R2OmegaHigh.outer_support
#print axioms WuPaper.R2OmegaHigh.inner_geometry
#print axioms WuPaper.R2OmegaHigh.theta_sum
#print axioms WuPaper.R2OmegaHigh.theta_atom_nonneg
#print axioms WuPaper.R2OmegaHigh.actual_atom_lower
end WuPaper.R2OmegaHigh
