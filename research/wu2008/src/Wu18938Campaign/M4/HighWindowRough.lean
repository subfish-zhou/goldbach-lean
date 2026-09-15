import Wu18938Campaign.M4.HighRough
import WR2GammaHighGeometry

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuSource.SrcSingle WuPaper.R2GammaHigh
open LiLiuPrereqBuchstab Finset Real
open scoped Classical

theorem original_lower_cutoff_power {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hdm : d ∈ psiPrimes (j.castAdd 4) N) :
    (N : ℝ) ^ (1 / 40 : ℝ) ≤
      wuLocalCutoff N δ d (Wu04RemainingCore.row j).S := by
  let k := j.castAdd 4
  have hg := seven_parameter_geometry k
  have hr := (seven_ratio_geometry k hN hd hh hdm).2.2
  have hS : 0 < psiTop k := by linarith [hg.2.2.1]
  have hbase : (1 / 40 : ℝ) ≤
      (1 / 2 - 1 / 100 - psiRight k) / psiTop k := hg.2.2.2.2.2.2.2.2.2.2
  have hexp : (1 / 40 : ℝ) ≤ (levelExponent δ - psiRight k) * (1 / psiTop k) := by
    have h := (le_div_iff₀ hS).mp hbase
    rw [mul_one_div]
    apply (le_div_iff₀ hS).mpr
    dsimp only [levelExponent]
    linarith only [h, hh]
  have hpow := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) _) hr
    (one_div_nonneg.mpr hS.le)
  rw [← rpow_mul (Nat.cast_nonneg N)] at hpow
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h := (rpow_le_rpow_of_exponent_le hN1 hexp).trans hpow
  change _ ≤ wuLocalCutoff N δ d (psiTop k) at h
  simpa only [k, (seven_source_rows.1 j).2] using h

theorem original_label_bounds {N d q : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hdm : d ∈ psiPrimes (j.castAdd 4) N)
    (hq : q ∈ primeWindow N
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)) :
    0 < q ∧ (N : ℝ) ^ (1 / 40 : ℝ) ≤ q ∧
      (q : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ) := by
  have hm := mem_primeWindow.mp hq
  have hc := (seven_cutoff_geometry (j.castAdd 4) hN hd hh hdm).2.2.1
  rw [(seven_source_rows.1 j).1] at hc
  exact ⟨hm.1.pos, (original_lower_cutoff_power j hN hd hh hdm).trans hm.2.2.1,
    hm.2.2.2.le.trans hc⟩

theorem original_prefix_buchstab_range {N d q n : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hdm : d ∈ psiPrimes (j.castAdd 4) N) (hn : n ≤ 6) (l : List ℕ)
    (hl : l ∈ secondFunctionalMotherTuples (primeWindow N
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)) n)
    (hq : q ∈ l) :
    2 < log ((N : ℝ) / (d * l.prod : ℕ)) / log q ∧
      log ((N : ℝ) / (d * l.prod : ℕ)) / log q ≤ 40 := by
  have htuple := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  have hlabels := fun p hp => original_label_bounds j hN hd hh hdm (htuple.2.2 p hp)
  have hdhi : (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    (mem_primeWindow.mp hdm).2.2.2.le.trans
      (rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega))
        (seven_parameter_geometry (j.castAdd 4)).2.2.2.2.2.2.2.2.2.1)
  exact six_label_buchstab_range hN (mem_primeWindow.mp hdm).1.pos l
    (htuple.1.le.trans hn) hdhi (fun p hp => ⟨(hlabels p hp).1, (hlabels p hp).2.2⟩)
    (hlabels q hq).2.1 (hlabels q hq).2.2

theorem original_prefix_rough_uniform {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ d ∈ psiPrimes (j.castAdd 4) N,
      ∀ n : ℕ, n ≤ 6 → ∀ l ∈ secondFunctionalMotherTuples (primeWindow N
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)) n,
      ∀ q ∈ l,
      ((roughNumbers ((N : ℝ) / (d * l.prod : ℕ)) q).card : ℝ) ≤
        (buchstab (log ((N : ℝ) / (d * l.prod : ℕ)) / log q) + ε) *
          ((N : ℝ) / (d * l.prod : ℕ)) / log q := by
  obtain ⟨T, hT4, hscalar⟩ := six_label_rough_uniform heps
  refine ⟨T, hT4, ?_⟩
  intro δ hd hh N hN j d hdm n hn l hl q hq
  have hN2 : 2 ≤ N := by omega
  have htuple := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  have hlabels := fun p hp => original_label_bounds j hN2 hd hh hdm (htuple.2.2 p hp)
  have hdhi : (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    (mem_primeWindow.mp hdm).2.2.2.le.trans
      (rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega))
        (seven_parameter_geometry (j.castAdd 4)).2.2.2.2.2.2.2.2.2.1)
  exact hscalar N hN d q (mem_primeWindow.mp hdm).1.pos l (htuple.1.le.trans hn) hdhi
    (fun p hp => ⟨(hlabels p hp).1, (hlabels p hp).2.2⟩)
    (hlabels q hq).2.1 (hlabels q hq).2.2

end Wu18938Campaign.M4
