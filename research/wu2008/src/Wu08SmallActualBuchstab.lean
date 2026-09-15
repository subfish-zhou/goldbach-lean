import Wu08SmallRoughUniform

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace Wu08FirstPrimeFour.SmallGrid
open Normalization

/-- The actual weighted and plain rectangle masses now have an unconditional
uniform bound by the explicit relaxed Buchstab prime sum. -/
theorem actualGrid_buchstab {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) →
    ∀ e : Bool, ∀ ξ ρ ε : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 → 0 ≤ ε →
      weightedGridMass N e ξ ρ+ε*plainGridMass N e ξ ρ ≤
        (ρ*(N : ℝ)/log N)*buchstabGrid N e ρ ε τ := by
  obtain ⟨Tr,hTr,hr⟩ := roughMass_buchstab hτ
  obtain ⟨Tb,hb⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le
      8 0 truncatedSixthLowerAlpha (by norm_num [truncatedSixthLowerAlpha]))
  refine ⟨max Tr Tb,hTr.trans (le_max_left _ _),?_⟩
  intro N hN e ξ ρ ε hξ hρ hρu hε
  have hNr : Tr ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hn4 := hTr.trans hNr
  have hlarge : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2 := by
    have hh : (8 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by
      simpa using hb N ((le_max_right _ _).trans hN)
    linarith
  exact (gridMass_le_relaxed hn4 hξ hρ hρu hlarge hε).trans
    ((relaxedMass_le_roughMass hn4 hρ hε).trans (hr N hNr e ρ ε hρ hρu hε))

/-- Genuine consumption of properMain_epsilon_normalized, not a theorem
conditional on knowing a grid mass estimate. The only remaining analytic
arrow is from the named, defined relaxed Buchstab sum to the original I. -/
theorem properMain_buchstab {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < 1/4 ∧ 0 < η ∧ η < 1/8 ∧
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
    ∀ e : Bool, ∀ ξ ρ : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 →
      properMain N e ξ ρ δ η ≤
        (wuSingularSeries N*(N : ℝ)/(log N)^2)*(ρ*buchstabGrid N e ρ ε τ) := by
  obtain ⟨δ,η,hδ,hδu,hη,hηu,Tp,hp⟩ := properMain_relaxed hε
  obtain ⟨Tr,hTr,hr⟩ := roughMass_buchstab hτ
  refine ⟨δ,η,hδ,hδu,hη,hηu,max Tp Tr,?_⟩
  intro N hN hEven e ξ ρ hξ hρ hρu
  have hNp : Tp ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNr : Tr ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hn4 : (4 : ℝ) ≤ N := hTr.trans hNr
  have hs : 0 ≤ wuSingularSeries N/log N := by
    rw [wuSingularSeries_eq_liu N (by exact_mod_cast (show (0 : ℝ) < N by linarith))]
    exact div_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
      (log_nonneg (by linarith))
  have hmass := (relaxedMass_le_roughMass hn4 hρ hε.le).trans
    (hr N hNr e ρ ε hρ hρu hε.le)
  exact (hp N hNp hEven e ξ ρ hξ hρ hρu).trans
    ((mul_le_mul_of_nonneg_left hmass hs).trans_eq (by ring))

/-- Exact logarithmic kernel with the physical rho dilation left explicit.
The four labels occur once each, and the rough cutoff remains the SECOND. -/
theorem roughX_log_identity {N : ℕ} {e : Bool} {ρ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ)
    {q : Quad} (hq : q ∈ relaxedQuads N e ρ) :
    log (roughX N ρ q)/log (q.2.1 : ℝ) =
      (1+log ρ/log N-log (q.1 : ℝ)/log N-log (q.2.1 : ℝ)/log N-
        log (q.2.2.1 : ℝ)/log N-log (q.2.2.2 : ℝ)/log N)/(log (q.2.1 : ℝ)/log N) := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  obtain ⟨ha,hb,hc,hd,_,_,hD,_⟩ := relaxed_data hN hρ hp
  have ha0 : (p.2 : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (p.1.1 : ℝ) ≠ 0 := by exact_mod_cast hb.ne_zero
  have hc0 : (p.1.2.1 : ℝ) ≠ 0 := by exact_mod_cast hc.ne_zero
  have hd0 : (p.1.2.2.1 : ℝ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hρ0 : ρ ≠ 0 := by linarith
  have hln : log (N : ℝ) ≠ 0 := (log_pos (by linarith : (1 : ℝ) < N)).ne'
  have hlb : log (p.1.1 : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hb.one_lt)).ne'
  simp only [roughX,quadProduct,quadOf,Nat.cast_mul]
  rw [log_div (mul_ne_zero hρ0 hN0) (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0) hd0),
    log_mul hρ0 hN0,log_mul (mul_ne_zero (mul_ne_zero ha0 hb0) hc0) hd0,
    log_mul (mul_ne_zero ha0 hb0) hc0,log_mul ha0 hb0]
  field_simp
  ring

#print axioms actualGrid_buchstab
#print axioms properMain_buchstab
#print axioms roughX_log_identity
end Wu08FirstPrimeFour.SmallGrid
