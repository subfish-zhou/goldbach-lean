import MathlibNt.Wu2008DoubleSieve.HighSixEndpoint
import MathlibNt.Wu2008DoubleSieve.Omega3SieveSource
import MathlibNt.Wu2008DoubleSieve.Omega3Relative
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralNormalization

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter
open scoped Classical Topology

noncomputable def W (N : ℕ) : Fin 1 → Finset ℕ := fun _ => P N

@[simp] theorem support (N : ℕ) : boxConvolutionSupport (W N) = P N :=
  SingleUpperCounts.single_support (P N)

@[simp] theorem coeff {N p : ℕ} (hp : p ∈ P N) : convolutionCoeff (W N) p = 1 := by
  exact (SingleUpperCounts.single_coeff (P N) p).trans (if_pos hp)

theorem weighted_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ boxConvolutionSupport (W N), (convolutionCoeff (W N) p : ℝ)*f p) =
      ∑ p ∈ P N, f p := SingleUpperCounts.single_weighted_sum (P N) f

theorem support_pos {N p : ℕ} (hp : p ∈ boxConvolutionSupport (W N)) : 0 < p :=
  (mem_primeWindow.mp ((support N) ▸ hp)).1.pos

/-- The exact single-coordinate convolution retains every ordered inner label. -/
theorem O3_eq (N : ℕ) (δ : ℝ) : O3 N δ = wuOmega3Sum N δ s S (W N) := by
  exact (weighted_sum N (fun p => wuOmega3 N p δ s S)).symm

/-- No squared-prefix condition is used in the finite switching map. -/
theorem switching_finite {N : ℕ} {δ : ℝ} (hN : 4 ≤ N) (he : Even N) :
    O3 N δ ≤ omega3SwitchedSiftedCount N δ s S
      (sqrt ((N : ℝ)^(1/2-δ))) (W N) + omega3BadDCount N δ s S (W N) +
      omega3ExceptionalOutputCount N δ s S (W N) := by
  rw [O3_eq]
  exact wuOmega3Sum_le_switched_add_badD_add_exceptional hN he
    (fun _ hp => support_pos hp)

/-- The true high-prime support remains below Q, but its square does not. -/
theorem support_geometry {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    0 < p ∧ p ≤ N ∧ (p : ℝ) ≤ (N : ℝ)^(1/2-δ) ∧
      1 < R N δ p ∧ R N δ p ≤ N ∧ (N : ℝ)^(1/6 : ℝ) ≤ R N δ p := by
  have hpp := (mem_primeWindow.mp hp).1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.pos
  have hQ : (N : ℝ)^(1/2-δ) ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNr
      (show 1/2-δ ≤ 1 by linarith)
  have hpQ : (p : ℝ) ≤ (N : ℝ)^(1/2-δ) :=
    (mem_primeWindow.mp hp).2.2.2.le.trans
      (rpow_le_rpow_of_exponent_le hNr (by norm_num [right]; linarith))
  have hr := ratio_bounds hN hδ hδhi hp
  refine ⟨hpp.pos, ?_, hpQ, hr.1, (div_le_self (by positivity) hp1).trans hQ, ?_⟩
  · exact_mod_cast hpQ.trans hQ
  · exact (rpow_le_rpow_of_exponent_le hNr (by norm_num [right]; linarith)).trans hr.2.2

/-- The actual logarithmic parameter is proved admissible before using sSup. -/
theorem phi_bounds {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    2 < omega3XPhi N p δ ∧ omega3XPhi N p δ ≤ 6 := by
  have hg := support_geometry hN hδ hδhi hp
  have hN0 : (0 : ℝ) < N := by positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hg.1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hg.1
  have hlN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hlR : 0 < log (R N δ p) := log_pos hg.2.2.2.1
  have hlp : 0 ≤ log (p : ℝ) := log_nonneg hp1
  have hlower := log_le_log (rpow_pos_of_pos hN0 _) hg.2.2.2.2.2
  rw [log_rpow hN0] at hlower
  have hlogR : log (R N δ p) = (1/2-δ)*log N-log p := by
    rw [R, log_div (rpow_pos_of_pos hN0 _).ne' hp0.ne', log_rpow hN0]
  have hlogNp : log ((N : ℝ)/p) = log N-log p := log_div hN0.ne' hp0.ne'
  change 2 < log ((N : ℝ)/p)/log (R N δ p) ∧
    log ((N : ℝ)/p)/log (R N δ p) ≤ 6
  constructor
  · rw [lt_div_iff₀ hlR, hlogR, hlogNp]
    nlinarith [mul_pos hδ hlN]
  · rw [div_le_iff₀ hlR, hlogNp]
    linarith

/-- The envelope is the inherited genuine supremum, not a selected maximum. -/
theorem integral_le_envelope {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    0 ≤ omega3XIntegral s S (omega3XPhi N p δ) ∧
      omega3XIntegral s S (omega3XPhi N p δ) ≤ omega3XIntegralEnvelope s S := by
  have hφ := (phi_bounds hN hδ hδhi hp).1.le
  exact ⟨omega3XIntegral_nonneg (by norm_num [s]) (by norm_num [s,S])
    (by norm_num [S]) hφ, omega3XIntegral_le_envelope (by norm_num [s])
    (by norm_num [s,S]) (by norm_num [S]) hφ⟩

/-- The original strict carrier enters the generic finite Rosser upper sieve.
The complete X and both physical remainders are retained, not assumed small. -/
theorem switched_density {δ ρ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      omega3SwitchedSiftedCount N δ s S (sqrt ((N : ℝ)^(1/2-δ))) (W N) ≤
        omega3SieveX N δ s S (W N) *
          (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
            wuSingularSeries N/log N) +
        omega3SieveR1 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S
          (sqrt ((N : ℝ)^(1/2-δ))) (W N) +
        omega3SieveR2 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S
          (sqrt ((N : ℝ)^(1/2-δ))) (W N) := by
  obtain ⟨T,hT4,hT⟩ := omega3_switched_upper_source_density hδ
    (show δ < 1/2 by linarith) hρ
  refine ⟨T,hT4,?_⟩
  intro N hN he
  exact (omega3_switched_sifted_le_closed N δ s S _ (W N)
    (fun _ hp => support_pos hp)).trans (hT N hN he 1 s S (W N))

end Wu2008DoubleSieve.HighSix.Omega3Upper
