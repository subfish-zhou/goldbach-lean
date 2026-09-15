import CoverMassFibre
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryPrimeMass

namespace CoverMass
open Finset Real Filter Wu2008DoubleSieve HighBoxRecovery
open scoped Classical Topology Interval
noncomputable section

/-- The original Delta range gives logarithmic width, without selecting a mesh. -/
theorem delta_log_bound {N : ℕ} {Δ : ℝ} (hL : 0 < log (N : ℝ))
    (hlo : 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ)
    (hhi : Δ < 1+2*log (N : ℝ)^(-4 : ℝ)) :
    1 < Δ ∧ log Δ ≤ 2/log (N : ℝ)^4 := by
  have hΔ : 1 < Δ := by have := rpow_pos_of_pos hL (-4 : ℝ); linarith
  have he : log (N : ℝ)^(-4 : ℝ) = 1/log (N : ℝ)^(4 : ℕ) := by
    rw [rpow_neg hL.le]; norm_num
  refine ⟨hΔ,?_⟩
  have hl := log_le_sub_one_of_pos (show 0 < Δ by linarith)
  rw [he,mul_one_div] at hhi
  linarith

/-- The whole r+2 prime window has its sharp logarithmic mass. Both forced
bands and the actual d*N divisor deletion are paid before moving endpoints.
This statement uses only the original terminal and includes s=2. -/
theorem full_grid_kernel {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ d : ℕ, 0 < d → d ≤ N → ∀ q D : ℝ,
      (N : ℝ)^(10*highEta) ≤ q → q ≤ D → D ≤ q*Δ^2 →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 → ∀ r : ℕ,
      reboxingAlpha q Δ 3 r ≤ q^(1/s) → q^(1/s) < reboxingAlpha q Δ 3 (r+1) →
      1 < Δ ∧ 1 < q ∧
      (∀ p ∈ primeWindow 1 (q^(1/3 : ℝ)) (reboxingAlpha q Δ 3 (r+2)),
        4 ≤ (p : ℝ) ∧ 1/4 ≤ 1-log (p : ℝ)/log D) ∧
      (∑ p ∈ primeWindow N (q^(1/3 : ℝ)) (reboxingAlpha q Δ 3 (r+2)),
        1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D))) ≤ log (2/(s-1))+ε := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨Tq,hTq4,hquad⟩ := HighO2Terminal.selected_fibre_integral (show 0 < ε/3 by positivity)
  obtain ⟨Td,hdelete⟩ := primeCoefficient_all_to_coprime_uniform
    (show 0 < highEta/2 by positivity) (show (0 : ℝ) ≤ 1 by norm_num) (show 0 < ε/3 by positivity)
  obtain ⟨Tb,hband⟩ := reboxing_short_prime_mass hη (show (0 : ℝ) < 4 by norm_num)
  have hlogt := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Tl,hloglarge⟩ := eventually_atTop.mp
    (hlogt.eventually (eventually_ge_atTop (max 1 (16/(10*highEta)))))
  obtain ⟨Tp,hpowlarge⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop (by decide : 5 ≠ 0)).comp hlogt).eventually
      (eventually_ge_atTop (48*(8/highEta+2)/ε)))
  obtain ⟨Th,hheight⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max 4 (max Tq (max Td (max Tb (max Tl (max Tp Th))))),le_max_left _ _,?_⟩
  intro N hN Δ hlo hhi d hd hdN q D hqlo hDlo hDhi s hs hs3 r hrlo hrhi
  have hN4 : 4 ≤ N := by omega
  have hNq : Tq ≤ N := by omega
  have hNd : Td ≤ N := by omega
  have hNb : Tb ≤ N := by omega
  have hNl : Tl ≤ N := by omega
  have hNp : Tp ≤ N := by omega
  have hNh : Th ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log (N : ℝ) := (le_max_left _ _).trans (hloglarge N hNl)
  have hL : 0 < log (N : ℝ) := by linarith
  obtain ⟨hΔ,hΔlog⟩ := delta_log_bound hL hlo hhi
  have hq : 1 < q := (one_lt_rpow hNr (show 0 < 10*highEta by positivity)).trans_le hqlo
  have hq0 : 0 < q := by linarith
  have hD : 1 < D := hq.trans_le hDlo
  have hD0 : 0 < D := by linarith
  have hLq : 10*highEta*log (N : ℝ) ≤ log q := by
    have h := log_le_log (rpow_pos_of_pos hN0 _) hqlo
    simpa only [log_rpow hN0] using h
  have hL4 : 1 ≤ log (N : ℝ)^(4 : ℕ) := one_le_pow₀ hL1
  have hΔ2 : log Δ ≤ 2 := hΔlog.trans ((div_le_iff₀ (by positivity)).mpr (by linarith))
  have hmesh : 8*log Δ ≤ log q := by
    have h := (div_le_iff₀ (show 0 < 10*highEta by positivity)).mp
      ((le_max_right _ _).trans (hloglarge N hNl))
    dsimp only [Function.comp_apply] at h
    nlinarith
  have hg := complete_endpoint_bounds hq hΔ hDlo hDhi hs (by linarith) hrlo hrhi
  let a := q^(1/3 : ℝ)
  let c := D^(1/3 : ℝ)
  let e := D^(1/s)
  let b := reboxingAlpha q Δ 3 (r+2)
  have haheight : (N : ℝ)^highEta ≤ a := by
    calc
      _ ≤ (N : ℝ)^((10*highEta)*(1/3)) := rpow_le_rpow_of_exponent_le hNr.le (by linarith)
      _ = ((N : ℝ)^(10*highEta))^(1/3 : ℝ) := rpow_mul hN0.le _ _
      _ ≤ _ := rpow_le_rpow (by positivity) hqlo (by norm_num)
  have hb0 : 0 < b := (rpow_pos_of_pos hD0 (1/s)).trans_le hg.2.2.1
  have hK : ∀ p ∈ primeWindow 1 a b,
      0 ≤ 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D)) ∧
      1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D)) ≤ 8/(p : ℝ) := by
    intro p hp
    have hh := mem_primeWindow.mp hp
    exact (enlarged_kernel_bound hq hΔ hDlo hs hmesh
      ((hheight N hNh).trans (haheight.trans hh.2.2.1)) (hh.2.2.2.le.trans hg.2.2.2)).2
  refine ⟨hΔ,hq,?_,?_⟩
  · intro p hp
    have hh := mem_primeWindow.mp hp
    have hp4 := (hheight N hNh).trans (haheight.trans hh.2.2.1)
    exact ⟨hp4,(enlarged_kernel_bound hq hΔ hDlo hs hmesh hp4 (hh.2.2.2.le.trans hg.2.2.2)).1⟩
  have hwidth := endpoint_log_widths hq hΔ hDlo hDhi hs hb0 hg.2.2.2
  have hwidth4 : 2*log Δ ≤ 4/log (N : ℝ)^4 := by
    calc
      _ ≤ 2*(2/log (N : ℝ)^4) := mul_le_mul_of_nonneg_left hΔlog (by norm_num)
      _ = _ := by ring
  have hlower := hband N hNb a c haheight hg.1 (hwidth.1.trans hwidth4)
  have hupper := hband N hNb e b (haheight.trans (hg.1.trans hg.2.1)) hg.2.2.1
    (hwidth.2.trans hwidth4)
  have hsplit := kernel_window_split hg.1 hg.2.1 hg.2.2.1 hK (N := N)
  have hquad' := hquad N hNq d hd hdN D (hqlo.trans hDlo) (fun _ => (1 : ℝ))
    (fun _ _ _ _ _ => le_rfl) (by intro u hu; norm_num) s 3 hs (by linarith) (by norm_num) (by norm_num)
  rw [kernel_exact hs (by linarith)] at hquad'
  norm_num only [show (3 : ℝ)-1=2 by norm_num] at hquad'
  have hdelheight : ((d*N : ℕ) : ℝ)^(highEta/2) ≤ c := by
    calc
      _ ≤ ((N : ℝ)^2)^(highEta/2) := by
        apply rpow_le_rpow (Nat.cast_nonneg _)
        · rw [Nat.cast_mul,pow_two]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdN) (Nat.cast_nonneg N)
        · positivity
      _ = (N : ℝ)^highEta := by
        rw [← rpow_two,← rpow_mul (Nat.cast_nonneg N)]; congr 1; ring
      _ ≤ _ := haheight.trans hg.1
  have hdelete' := hdelete (d*N) (hNd.trans (by nlinarith)) D c e (fun _ => (1 : ℝ)) hD hdelheight
    (rpow_le_rpow_of_exponent_le hD.le (one_div_le_one_div_of_le (by norm_num) hs))
    (by intro p hp; norm_num)
  have hmid : (∑ p ∈ primeWindow 1 c e, 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D))) ≤
      log (2/(s-1))+2*(ε/3) := by
    have h1 := (abs_le.mp hquad').2
    have h2 := (abs_le.mp hdelete').2
    dsimp [c,e] at h2 ⊢
    linarith
  have hpay : 16*((8/highEta+2)/log (N : ℝ)^5) ≤ ε/3 := by
    have h := (div_le_iff₀ hε).mp (hpowlarge N hNp)
    dsimp only [Function.comp_apply] at h
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hbandpay : 8*((∑ p ∈ primeWindow N a c, (1 : ℝ)/p)+
      (∑ p ∈ primeWindow N e b, (1 : ℝ)/p)) ≤ ε/3 := by
    have hl : (∑ p ∈ primeWindow N a c, (1 : ℝ)/p) ≤ (8/highEta+2)/log (N : ℝ)^5 := by
      simpa only [show (2 : ℝ)*4=8 by norm_num] using hlower
    have hu : (∑ p ∈ primeWindow N e b, (1 : ℝ)/p) ≤ (8/highEta+2)/log (N : ℝ)^5 := by
      simpa only [show (2 : ℝ)*4=8 by norm_num] using hupper
    linarith
  exact hsplit.trans (by linarith [hmid,hbandpay])

end
end CoverMass
