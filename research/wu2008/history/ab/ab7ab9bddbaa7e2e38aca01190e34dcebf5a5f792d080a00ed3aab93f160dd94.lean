import WSrcSingleCount
import HighFullLocal
import HighO2TerminalFinal
import HighO3Envelope

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighBoxRecovery
open Finset Real Filter
open scoped Classical Topology Interval BigOperators
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

def index (j : Fin 4) : Fin 7 := Fin.natAdd 3 j
def windows (j : Fin 4) (N : ℕ) : Fin 1 → Finset ℕ := fun _ => psiPrimes (index j) N
def theta (j : Fin 4) (N : ℕ) (δ : ℝ) : ℝ :=
  boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (windows j N)
def lowerIntegral (j : Fin 4) : ℝ :=
  ∫ u in (1 - 1 / psiNode (index j))..(1 - 1 / psiTop (index j)),
    log (psiTop (index j) * u - 1) / (u * (1 - u))

theorem support (j : Fin 4) (N : ℕ) :
    boxConvolutionSupport (windows j N) = psiPrimes (index j) N :=
  SingleUpperCounts.single_support _

theorem weighted_sum (j : Fin 4) (N : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ boxConvolutionSupport (windows j N),
      (convolutionCoeff (windows j N) p : ℝ) * f p) =
        ∑ p ∈ psiPrimes (index j) N, f p :=
  SingleUpperCounts.single_weighted_sum _ _

theorem geometry (j : Fin 4) :
    2 ≤ psiNode (index j) ∧ psiNode (index j) ≤ 3 ∧
    3 ≤ psiTop (index j) ∧ psiTop (index j) ≤ 5 ∧
    psiNode (index j) ≤ psiTop (index j) ∧
    2 ≤ psiTop (index j) - psiTop (index j) / psiNode (index j) ∧
    (1 / 15 : ℝ) ≤ psiLeft (index j) ∧
    psiLeft (index j) ≤ psiRight (index j) ∧
    psiRight (index j) ≤ 1 / 3 ∧
    psiRight (index j) ≤ 1 / 2 - 100 * highEta ∧
    (1 / 6 : ℝ) ≤ 1 / 2 - 1 / 100 - psiRight (index j) := by
  fin_cases j <;> norm_num [index, psiNode, psiTop, psiLeft, psiRight,
    sourceNode, truncatedSixthLowerAlpha, highEta]

theorem prime_geometry {N p : ℕ} (j : Fin 4) (hN : 2 ≤ N)
    (hp : p ∈ psiPrimes (index j) N) :
    p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ highEta ≤ p ∧
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 2 - 100 * highEta) := by
  have hm := mem_primeWindow.mp hp
  have hg := geometry j
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  refine ⟨hm.1, hm.2.1, ?_, ?_⟩
  · exact (rpow_le_rpow_of_exponent_le hn
      ((by norm_num [highEta] : highEta ≤ 1 / 15).trans hg.2.2.2.2.2.2.1)).trans hm.2.2.1
  · exact hm.2.2.2.le.trans
      (rpow_le_rpow_of_exponent_le hn hg.2.2.2.2.2.2.2.2.2.1)

theorem support_geometry {N : ℕ} {δ : ℝ} (j : Fin 4)
    (hN : 2 ≤ N) (hh : δ ≤ 1 / 100) :
    (∀ k p, p ∈ windows j N k → p.Prime ∧ (N : ℝ) ^ highEta ≤ p) ∧
    (∀ d ∈ boxConvolutionSupport (windows j N),
      (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ - 10 * highEta)) := by
  refine ⟨fun _ p hp => ⟨(prime_geometry j hN hp).1, (prime_geometry j hN hp).2.2.1⟩, ?_⟩
  intro d hd
  rw [support] at hd
  apply (prime_geometry j hN hd).2.2.2.trans
  apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  norm_num [highEta]
  linarith

theorem scale_nonneg {N : ℕ} (hN : 2 ≤ N) : 0 ≤ truncatedSixthMassScale N := by
  have := (wuSingularSeries_pos N (show 0 < N by omega)).le
  unfold truncatedSixthMassScale
  positivity

theorem theta_nonneg {N : ℕ} {δ : ℝ} (j : Fin 4)
    (hN : 4 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) : 0 ≤ theta j N δ := by
  have hg := support_geometry j (by omega) hh
  have ht := HighO3.theta_singular (windows j N) hN hd (by linarith)
    (show 0 < highEta by norm_num [highEta])
    (fun d hdm => ⟨boxConvolutionSupport_pos (fun k p hp => (hg.1 k p hp).1.pos) hdm,
      hg.2 d hdm⟩)
  have hr : 0 ≤ boxConvolutionReciprocalMass (windows j N) :=
    sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d))
  have hC := (wuSingularSeries_pos N (show 0 < N by omega)).le
  exact (by positivity : 0 ≤ 2 * wuSingularSeries N * N / log N ^ 2 *
    boxConvolutionReciprocalMass (windows j N)).trans ht

theorem theta_total_mass {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      0 ≤ theta j N δ ∧ theta j N δ ≤ 480 * truncatedSixthMassScale N := by
  obtain ⟨T1, hT14, hm⟩ := SingleUpperPrimePayment.reciprocal_mass_bound
  obtain ⟨T2, _, hp⟩ := SingleUpperPrimePayment.denominator_payment (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T3, _, hl⟩ := SingleUpperPrimePayment.trueLi_upper (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN _he j
  have hN4 : 4 ≤ N := hT14.trans (by omega)
  have hN2 : 2 ≤ N := by omega
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN2)
  have hC := (wuSingularSeries_pos N (show 0 < N by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN2)
  have hg := geometry j
  have hden (p : ℕ) (hp' : p ∈ psiPrimes (index j) N) :
      2 < p ∧ 1 / ((p : ℝ) - 2) ≤ 2 / p := by
    have h := hp N (by omega) p (mem_primeWindow.mp hp').1
      ((rpow_le_rpow_of_exponent_le hn hg.2.2.2.2.2.2.1).trans
        (mem_primeWindow.mp hp').2.2.1)
    exact ⟨h.1, by norm_num at h ⊢; exact h.2.1⟩
  have hsum : (∑ p ∈ psiPrimes (index j) N, 1 / ((p : ℝ) - 2)) ≤ 10 := by
    have hsub : psiPrimes (index j) N ⊆
        LiLiuPrereqBuchstab.primesIcc ((N : ℝ) ^ psiLeft (index j)) ((N : ℝ) ^ psiRight (index j)) := by
      intro p hpm
      have hx := mem_primeWindow.mp hpm
      exact (LiLiuPrereqBuchstab.mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr
        ⟨hx.1, hx.2.2.1, hx.2.2.2.le⟩
    calc
      _ ≤ ∑ p ∈ psiPrimes (index j) N, 2 / (p : ℝ) :=
        sum_le_sum (fun p hpm => (hden p hpm).2)
      _ = 2 * ∑ p ∈ psiPrimes (index j) N, 1 / (p : ℝ) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ 2 * ∑ p ∈ LiLiuPrereqBuchstab.primesIcc
          ((N : ℝ) ^ psiLeft (index j)) ((N : ℝ) ^ psiRight (index j)), 1 / (p : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity))
          (by norm_num)
      _ ≤ 10 := by
        have h := hm N (by omega) _ _ hg.2.2.2.2.2.2.1
          hg.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.1
        linarith
  have hgap (p : ℕ) (hp' : p ∈ psiPrimes (index j) N) :
      (1 / 6 : ℝ) ≤ (1 / 2 - δ) - log (p : ℝ) / log N := by
    have hc : log (p : ℝ) / log N ≤ psiRight (index j) := by
      apply (div_le_iff₀ hlog).mpr
      rw [← log_rpow (show (0 : ℝ) < N by positivity)]
      exact log_le_log (by exact_mod_cast (mem_primeWindow.mp hp').1.pos)
        (mem_primeWindow.mp hp').2.2.2.le
    linarith [hg.2.2.2.2.2.2.2.2.2.2]
  have hweighted : (∑ p ∈ psiPrimes (index j) N,
      1 / (((p : ℝ) - 2) * ((1 / 2 - δ) - log p / log N))) ≤ 60 := by
    calc
      _ ≤ ∑ p ∈ psiPrimes (index j) N, 6 * (1 / ((p : ℝ) - 2)) := by
        apply sum_le_sum
        intro p hpm
        have hp2 : (2 : ℝ) < p := by exact_mod_cast (hden p hpm).1
        have hgap' := hgap p hpm
        have hi : 1 / ((1 / 2 - δ) - log (p : ℝ) / log N) ≤ 6 :=
          (div_le_iff₀ (by linarith)).mpr (by linarith)
        calc
          _ = (1 / ((p : ℝ) - 2)) * (1 / ((1 / 2 - δ) - log p / log N)) := by ring
          _ ≤ (1 / ((p : ℝ) - 2)) * 6 := mul_le_mul_of_nonneg_left hi (by positivity)
          _ = _ := by ring
      _ = 6 * ∑ p ∈ psiPrimes (index j) N, 1 / ((p : ℝ) - 2) := (mul_sum ..).symm
      _ ≤ 60 := by linarith
  have hcoef : 4 * logarithmicIntegral N * wuSingularSeries N / log N ≤
      8 * truncatedSixthMassScale N := by
    calc
      _ ≤ 4 * ((1 + 1) * (N : ℝ) / log N) * wuSingularSeries N / log N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hl N (by omega)) (by norm_num)) hC) hlog.le
      _ = _ := by unfold truncatedSixthMassScale; ring
  refine ⟨theta_nonneg j hN4 hd hh, ?_⟩
  rw [theta, windows, SingleUpperNormalization.theta_single_exact hN2 _
    (fun p hpm => ⟨(mem_primeWindow.mp hpm).1, (hden p hpm).1, (mem_primeWindow.mp hpm).2.1⟩)]
  calc
    _ ≤ (4 * logarithmicIntegral N * wuSingularSeries N / log N) * 60 :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ (8 * truncatedSixthMassScale N) * 60 := mul_le_mul_of_nonneg_right hcoef (by norm_num)
    _ = _ := by ring

#check @WuPaper.R2OmegaHigh.index
#check @WuPaper.R2OmegaHigh.windows
#check @WuPaper.R2OmegaHigh.theta
#check @WuPaper.R2OmegaHigh.lowerIntegral
#check @WuPaper.R2OmegaHigh.support
#check @WuPaper.R2OmegaHigh.weighted_sum
#check @WuPaper.R2OmegaHigh.geometry
#check @WuPaper.R2OmegaHigh.prime_geometry
#check @WuPaper.R2OmegaHigh.support_geometry
#check @WuPaper.R2OmegaHigh.scale_nonneg
#check @WuPaper.R2OmegaHigh.theta_nonneg
#check @WuPaper.R2OmegaHigh.theta_total_mass
#print axioms WuPaper.R2OmegaHigh.index
#print axioms WuPaper.R2OmegaHigh.windows
#print axioms WuPaper.R2OmegaHigh.theta
#print axioms WuPaper.R2OmegaHigh.lowerIntegral
#print axioms WuPaper.R2OmegaHigh.support
#print axioms WuPaper.R2OmegaHigh.weighted_sum
#print axioms WuPaper.R2OmegaHigh.geometry
#print axioms WuPaper.R2OmegaHigh.prime_geometry
#print axioms WuPaper.R2OmegaHigh.support_geometry
#print axioms WuPaper.R2OmegaHigh.scale_nonneg
#print axioms WuPaper.R2OmegaHigh.theta_nonneg
#print axioms WuPaper.R2OmegaHigh.theta_total_mass
end WuPaper.R2OmegaHigh
