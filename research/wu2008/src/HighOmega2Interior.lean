import HighOmega2Grid
import MathlibNt.Wu2008DoubleSieve.Omega2Parameter

namespace HighOmega2
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- The source terminal integer exists uniformly on the original high boxes;
all its properties are universal and it is never numerically evaluated. -/
theorem original_terminal {N : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδ : δ ≤ 50*highEta) (hΔ : 1 < Δ)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hr : OriginalRectangles N V)
    (hs : 2 ≤ s) (hst : s ≤ t) :
    let q := (N : ℝ)^(1/2-δ)/(∏ j, V j)
    1 < q ∧ ∃! r : ℕ, reboxingAlpha q Δ t r ≤ q^(1/s) ∧ q^(1/s) < reboxingAlpha q Δ t (r+1) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hVp : ∀ j, 0 < V j := fun j => (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hV j)
  have hprod := original_rectangles_product hN (fun j => (hVp j).le) hr
  have hη : 0 < highEta := by norm_num [highEta]
  have hq : 1 < (N : ℝ)^(1/2-δ)/(∏ j, V j) := by
    apply (one_lt_div (prod_pos (fun j _ => hVp j))).mpr
    exact hprod.trans_lt (rpow_lt_rpow_of_exponent_lt hN1 (by linarith))
  refine ⟨hq,?_⟩
  obtain ⟨r,hr'⟩ := reboxingAlpha_exists_terminal hq.le hΔ (show 0 < s by linarith) hst
  exact ⟨r,hr',fun n hn => reboxingAlpha_terminal_unique (by linarith) hΔ hn hr'⟩

/-- Literal internal windows are all cells with 1≤j<r. The left index is
forced by Fin 2/t≤1, and the right endpoint is the source terminal. -/
theorem interior_window {N r j : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 0 < N) (hΔ : 1 < Δ) (hV : ∀ l, 0 < V l)
    (hs : 2 ≤ s) (ht : 3 ≤ t) (hj : 1 ≤ j) (hjr : j < r)
    (hr : reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t r ≤
      ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s)) :
    ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t j ⊆
        primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) := by
  have hQ : 0 < (N : ℝ)^(1/2-δ) := rpow_pos_of_pos (by exact_mod_cast hN) _
  let q := (N : ℝ)^(1/2-δ)/(∏ l, V l)
  have hq : 0 < q := div_pos hQ (prod_pos (fun l _ => hV l))
  have hΔp : 0 < Δ := by linarith
  intro d hd p hp
  obtain ⟨hpp,hpc,hpl,hpu⟩ := mem_primeWindow.mp hp
  have hc := reboxing_support_cutoff_bounds hQ.le hΔp hV (show 0 < t by linarith) hd
  have hlow : wuLocalCutoff N δ d t ≤ reboxingAlpha q Δ t j := by
    apply hc.2.trans
    apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hq.le _)
    apply rpow_le_rpow_of_exponent_le hΔ.le
    have htw : (2 : ℝ)/t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    exact htw.trans (by exact_mod_cast hj)
  have hu : reboxingAlpha q Δ t (j+1) ≤ wuLocalCutoff N δ d s := by
    calc
      _ ≤ reboxingAlpha q Δ t r := (reboxingAlpha_strictMono hq hΔ).monotone (by exact_mod_cast hjr)
      _ ≤ q^(1/s) := hr
      _ ≤ _ := (reboxing_support_cutoff_bounds hQ.le hΔp hV (show 0 < s by linarith) hd).1
  exact mem_primeWindow.mpr ⟨hpp,hpc,hlow.trans hpl,hpu.trans_le hu⟩

/-- Fixed-cutoff lower parameter at the *upper* endpoint of each inner cell.
The original s,t domain keeps this actual parameter in [2,4]. -/
def lowerParameter (q Δ t : ℝ) (j : ℕ) : ℝ :=
  t*(1-log (reboxingAlpha q Δ t (j+1))/log q)

theorem lowerParameter_domain {q Δ s t : ℝ} {r j : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ) (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hcondition : 2 ≤ t-t/s) (hjr : j < r)
    (hr : reboxingAlpha q Δ t r ≤ q^(1/s)) :
    2 ≤ lowerParameter q Δ t j ∧ lowerParameter q Δ t j ≤ 4 := by
  have hlo : q^(1/t) ≤ reboxingAlpha q Δ t (j+1) := by
    rw [← reboxingAlpha_zero q Δ t]
    exact (reboxingAlpha_strictMono (by linarith) hΔ).monotone (by positivity)
  have hhi : reboxingAlpha q Δ t (j+1) ≤ q^(1/s) :=
    ((reboxingAlpha_strictMono (by linarith) hΔ).monotone (by exact_mod_cast hjr)).trans hr
  have hh := omega2_fixed_cutoff_domain hq hs ht hcondition hlo hhi
  exact ⟨hh.1,hh.2.trans (by linarith)⟩

/-- The lower insertion cutoff is above the literal Omega2 fixed cutoff.
Both the local d variation and the upper prime endpoint are accounted for. -/
theorem lowerParameter_cutoff {N d p j : ℕ} {δ q Δ t : ℝ}
    (hq : 1 < q) (hqD : q ≤ (N : ℝ)^(1/2-δ)/d)
    (ht : 3 ≤ t)
    (hparam : 0 < lowerParameter q Δ t j)
    (hp : p ∈ cell N q Δ t j) :
    wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ (d*p) (lowerParameter q Δ t j) := by
  let D := (N : ℝ)^(1/2-δ)/d
  let U := reboxingAlpha q Δ t (j+1)
  let u := lowerParameter q Δ t j
  have hD : 1 < D := hq.trans_le hqD
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have hpU : (p : ℝ) ≤ U := (mem_primeWindow.mp hp).2.2.2.le
  have hU1 : 1 ≤ U := (by exact_mod_cast (mem_primeWindow.mp hp).1.one_lt : (1 : ℝ) < p).le.trans hpU
  have hlog : log (p : ℝ)/log D ≤ log U/log q := by
    calc
      _ ≤ log U/log D := div_le_div_of_nonneg_right (log_le_log hp0 hpU) (log_pos hD).le
      _ ≤ _ := div_le_div_of_nonneg_left (log_nonneg hU1) (log_pos hq) (log_le_log (by linarith) hqD)
  have hcompare : u ≤ t*(1-log (p : ℝ)/log D) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hlog 1) (by linarith)
  have hidentity := omega2_fixed_cutoff_ratio hD hp0 (show 0 < t by linarith)
  have hlw : 0 < log (D^(1/t)) := log_pos (one_lt_rpow hD (by positivity))
  rw [← hidentity] at hcompare
  have hcross := (le_div_iff₀ hlw).mp hcompare
  have hfinal : log (D^(1/t)) ≤ log ((D/(p : ℝ))^(1/u)) := by
    rw [log_rpow (div_pos (by linarith : 0 < D) hp0)]
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hparam).mpr (by nlinarith)
  have hres := (log_le_log_iff (rpow_pos_of_pos (by linarith : 0 < D) _)
    (rpow_pos_of_pos (div_pos (by linarith : 0 < D) hp0) _)).mp hfinal
  simpa only [wuLocalCutoff,Nat.cast_mul,div_div,D,u] using hres

end
end HighOmega2
