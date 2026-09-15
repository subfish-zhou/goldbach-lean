import MathlibNt.Wu2008DoubleSieve.HighSixFinite
import MathlibNt.Wu2008DoubleSieve.ReboxingNormalization

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Exact two-coordinate expansion; equal products retain both ordered labels. -/
theorem double_AP_expansion (N Q : ℕ) (A B : Finset ℕ) :
    convolutionAPError N Q (Fin.cons B (fun _ : Fin 1 => A)) =
      ∑ p ∈ A, ∑ q ∈ B,
        ∑ r ∈ (Icc 1 (Q/(p*q))).filter (fun r => r.Coprime ((p*q)*N)),
          |primeAPError N (p*q*r) N| := by
  rw [convolutionAPError_eq_support_sum]
  change (∑ d ∈ boxConvolutionSupport (Fin.cons B (fun _ : Fin 1 => A)),
    (convolutionCoeff (Fin.cons B (fun _ : Fin 1 => A)) d : ℝ) *
      ∑ r ∈ (Icc 1 (Q/d)).filter (fun r => r.Coprime (d*N)),
        |primeAPError N (d*r) N|) = _
  rw [boxConvolution_sum_cons]
  exact SingleUpperCounts.single_weighted_sum A _

/-- Full-label cutoffs may vary even at equal products. Only the positive AP
majorant is enlarged; the signed sum itself is never treated as monotone. -/
theorem double_masked_remainder_le (N Q : ℕ) (A B : Finset ℕ)
    (V : ℕ → Finset ℕ) (hV : ∀ p ∈ A, V p ⊆ B)
    (upper : Bool) (D : ℕ → ℕ → ℕ) (cut : ℕ → ℕ → ℝ)
    (hD : ∀ p ∈ A, ∀ q ∈ V p, D p q ≤ Q/(p*q)+1) :
    |∑ p ∈ A, ∑ q ∈ V p, ordinaryRosserRemainder upper N (p*q) (D p q) (cut p q)| ≤
      convolutionAPError N Q (Fin.cons B (fun _ : Fin 1 => A)) := by
  rw [double_AP_expansion]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ q ∈ V p,
        ∑ r ∈ (Icc 1 (Q/(p*q))).filter (fun r => r.Coprime ((p*q)*N)),
          |primeAPError N (p*q*r) N| := by
      apply sum_le_sum
      intro q hq
      exact ordinaryRosserRemainder_le_AP (cut p q) (hD p hp q hq)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (hV p hp)
      (fun q _ _ => sum_nonneg (fun r _ => abs_nonneg _))

/-- Genuine depth-two BV; constants precede both windows, the moving mask,
all signs and every label-dependent cutoff. No single-prime BV is used. -/
theorem double_masked_bv {β δ A : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ U V : Finset ℕ,
      (∀ p ∈ U, p.Prime ∧ p.Coprime N ∧ (N : ℝ)^β ≤ (p : ℝ)) →
      (∀ q ∈ V, q.Prime ∧ q.Coprime N ∧ (N : ℝ)^β ≤ (q : ℝ)) →
      ∀ W : ℕ → Finset ℕ, (∀ p ∈ U, W p ⊆ V) →
      ∀ upper : Bool, ∀ D : ℕ → ℕ → ℕ, ∀ cut : ℕ → ℕ → ℝ,
      (∀ p ∈ U, ∀ q ∈ W p, D p q ≤ convolutionModulusCutoff N δ/(p*q)+1) →
      |∑ p ∈ U, ∑ q ∈ W p,
        ordinaryRosserRemainder upper N (p*q) (D p q) (cut p q)| ≤
          C*N/log (N : ℝ)^A := by
  obtain ⟨C, hC, T, hb⟩ := convolution_bombieri_vinogradov 2 hβ hδ hA
  refine ⟨C, hC, T, ?_⟩
  intro N hN U V hU hV W hW upper D cut hD
  apply (double_masked_remainder_le N _ U V W hW upper D cut hD).trans
  apply hb N hN 2 le_rfl (Fin.cons V (fun _ : Fin 1 => U))
  intro j
  exact Fin.cases (fun p hp => hV p hp) (fun _ p hp => hU p hp) j

/-- The actual moving pair remainder is uniformly logarithmically small. -/
theorem pair_bv {δ A : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |pairRemainder N δ| ≤ C*N/log (N : ℝ)^A := by
  obtain ⟨C, hC, T, hb⟩ := double_masked_bv (by norm_num : (0 : ℝ) < 1/25) hδ hA
  refine ⟨C, hC, max 4 T, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let V := primeWindow N ((N : ℝ)^(1/25 : ℝ)) ((N : ℝ)^alpha)
  have hp : ∀ p ∈ P N, p.Prime ∧ p.Coprime N ∧ (N : ℝ)^(1/25 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    have hm := mem_primeWindow.mp hp
    exact ⟨hm.1, hm.2.1,
      (rpow_le_rpow_of_exponent_le hN1 (by norm_num [left])).trans hm.2.2.1⟩
  have hV : ∀ q ∈ V, q.Prime ∧ q.Coprime N ∧ (N : ℝ)^(1/25 : ℝ) ≤ (q : ℝ) := by
    intro q hq
    have hm := mem_primeWindow.mp hq
    exact ⟨hm.1, hm.2.1, hm.2.2.1⟩
  have hsub : ∀ p ∈ P N, primeWindow N (z N δ p) (w N δ p) ⊆ V := by
    intro p hp q hq
    have hm := mem_primeWindow.mp hq
    exact mem_primeWindow.mpr ⟨hm.1, hm.2.1,
      (inner_lower_cutoff hN2 hδ hδhi hp).trans hm.2.2.1,
      hm.2.2.2.trans_le (cutoff_geometry hN2 hδ hδhi hp).2.2.1⟩
  exact hb N (by omega) (P N) V hp hV
    (fun p => primeWindow N (z N δ p) (w N δ p)) hsub false
    (fun p q => wuVariableRosserLevel N δ (p*q)) (fun p _ => z N δ p)
    (fun p _ q _ => (wuVariableRosserLevel_eq_combined N (p*q) δ).le)

/-- A single global epsilon pays the entire actual signed pair remainder. -/
theorem pair_remainder_small {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |pairRemainder N δ| ≤ ε * truncatedSixthMassScale N := by
  obtain ⟨C, hC, T, _, hBV⟩ := pair_bv hδ hδhi (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (C/(ε*wuSingularSeries 1))))
  refine ⟨max 4 (max T M), le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ N := (le_max_left T M).trans ((le_max_right _ _).trans hN)
  have hNM : M ≤ N := (le_max_right T M).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hbudget : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hC1)).mp (hM N hNM)
    have hs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hseries hε.le) hlog.le
    nlinarith
  have hb := hBV N hNT
  have hb' : |pairRemainder N δ| ≤ C * N / log (N : ℝ)^(3 : ℕ) := by
    convert hb using 1
    norm_num
  calc
    _ ≤ C * N / log (N : ℝ)^(3 : ℕ) := hb'
    _ = (C / log (N : ℝ)) * ((N : ℝ)/log (N : ℝ)^(2 : ℕ)) := by ring
    _ ≤ (ε * wuSingularSeries N) * ((N : ℝ)/log (N : ℝ)^(2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

/-- Actual Omega2 lower bound with BV already paid. The remaining main term
is the genuine finite lower Rosser main, not yet the classical J integral. -/
theorem omega2_lower_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      pairMain N δ - ε * truncatedSixthMassScale N ≤ O2 N δ := by
  obtain ⟨T, hT4, hT⟩ := pair_remainder_small hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN
  have hf := omega2_finite_lower (show 2 ≤ N by omega) hδ hδhi
  have hb := (abs_le.mp (hT N hN)).1
  linarith

/-- Nonconditional count consumption of the paid lower Rosser main. -/
theorem count_lower_main_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      2*C6 N ≤ O1 N δ - pairMain N δ + O3 N δ + ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hT⟩ := omega2_lower_paid hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN
  have hf := count_finite (show 2 ≤ N by omega) hδ hδhi
  have hb := hT N hN
  linarith

end Wu2008DoubleSieve.HighSix
