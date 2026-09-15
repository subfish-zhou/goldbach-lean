import Wu18938Campaign.M1.Confirmed.Buchstab
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitBoxedSigma

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem roughBox_log_geometry {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < log ((N : ℝ) ^ (1 / 2 - δ) / d) ∧
    η * log (N : ℝ) ≤ log ((N : ℝ) ^ (1 / 2 - δ) / d) ∧
    7 / 2 ≤ omega3XPhi N d δ ∧ omega3XPhi N d δ ≤ 1 / η := by
  have hg := hb.support_geometry hN hη hδ hd
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hg.1
  have hlog := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
  have hlogR := log_pos hg.2.2.1
  have hrem := log_le_log (rpow_pos_of_pos hNr η) (hb.remaining d hd)
  rw [log_rpow hNr] at hrem
  have hdlo := log_le_log (rpow_pos_of_pos hNr (3 / 10)) (hb.support_large d hd)
  rw [log_rpow hNr] at hdlo
  have hdlog : 0 ≤ log (d : ℝ) := log_nonneg (by exact_mod_cast hg.1)
  have hlogR_eq : log ((N : ℝ) ^ (1 / 2 - δ) / d) =
      (1 / 2 - δ) * log N - log d := by
    rw [log_div (rpow_pos_of_pos hNr _).ne' hdr.ne', log_rpow hNr]
  have hlogX_eq : log ((N : ℝ) / d) = log N - log d := log_div hNr.ne' hdr.ne'
  refine ⟨hlogR, hrem, ?_, ?_⟩
  · unfold omega3XPhi
    apply (le_div_iff₀ hlogR).mpr
    rw [hlogX_eq, hlogR_eq]
    nlinarith only [hdlo, hδ, hlog]
  · unfold omega3XPhi
    apply (div_le_iff₀ hlogR).mpr
    have hh : log (N : ℝ) ≤ log ((N : ℝ) ^ (1 / 2 - δ) / d) / η :=
      (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hrem)
    rw [div_eq_mul_inv, mul_comm _ η⁻¹] at hh
    rw [hlogX_eq]
    simpa only [one_div] using (sub_le_self (log (N : ℝ)) hdlog).trans hh

theorem roughBox_log_scale {m i N d : ℕ} {η δ Δ ε : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (he : 0 ≤ ε) :
    (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) * (ε * η) ≤
      ε * ((N : ℝ) / log N) / d := by
  have hl := roughBox_log_geometry hb hN hη hδ hd
  have hlog := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
  have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg N)
    (mul_pos hη hlog) hl.2.1
  calc
    _ = ((N : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)) * ((ε * η) / d) := by ring
    _ ≤ ((N : ℝ) / (η * log N)) * ((ε * η) / d) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

end Wu18938Campaign.M1.Confirmed
