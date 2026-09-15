import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitMassTheta

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSieve
open Real Finset HighUnitSource

/-- The original unit source normalized to Theta, retaining the fixed-delta factor. -/
theorem mother_unit_pair_theta_rho (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let K := unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
        unitLogCap21 (1/p.kappa3) (1/p.s)
      let a0 := fun d => wuLocalCutoff N δ d p.S
      let a1 := fun d => wuLocalCutoff N δ d p.kappa1
      let a2 := fun d => wuLocalCutoff N δ d p.kappa2
      let a3 := fun d => wuLocalCutoff N δ d p.kappa3
      let b := fun d => wuLocalCutoff N δ d p.s
      FourPrimeUnit.source N W a0 a1 a2 a3 b word20 +
        FourPrimeUnit.source N W a0 a1 a2 a3 b word21 ≤
        (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) * K/4 + ε) *
          boxTheta N ((N:ℝ)^(1/2-δ)) W := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hden : 0 < 1-2*δ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have he : 0 < ε/2 := by positivity
  have hem : 0 < ε/(2*A) := by positivity
  obtain ⟨T1,hT1,hd⟩ := mother_unit_pair_density k hδ hδhi hρ he
  obtain ⟨T2,_,hm⟩ := mother_boxed_mass_pair_theta k hδ hδhi hem
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hd' := hd N ((le_max_left _ _).trans hN) hn i Δ V hb p hp hs
  have hm' := mul_le_mul_of_nonneg_left
    (hm N ((le_max_right _ _).trans hN) i Δ V hb p hp hs) hA.le
  dsimp only at hd' hm' ⊢
  have hc : A*(ε/(2*A)) = ε/2 := by field_simp
  have hleft (x c : ℝ) : x*(A*c/log N) = A*(c/log N*x) := by ring
  have hright (K Θ : ℝ) : A*((K/4+ε/(2*A))*Θ) = (A*K/4+ε/2)*Θ := by
    calc
      _ = (A*K/4+A*(ε/(2*A)))*Θ := by ring
      _ = _ := by rw [hc]
  rw [hleft] at hd'
  rw [hright] at hm'
  nlinarith only [hd',hm']

/-- A single positive auxiliary rho pays an error uniformly over all compact caps. -/
theorem rho_budget {δ ε : ℝ} (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ K : ℝ, 0 ≤ K → K ≤ 2000 →
      ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) * K/4 ≤
        (2/(1-2*δ))*K + ε := by
  let A := 2/(1-2*δ)
  let e := exp (-eulerMascheroniConstant)
  let t := 1+2*e
  have hden : 0 < 1-2*δ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have he : 0 < e := exp_pos _
  have ht : 0 < t := by dsimp [t]; positivity
  let ρ := min 1 (ε/(A*2000*t))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hr1 : ρ ≤ 1 := min_le_left _ _
  have hpay : (A*2000*t)*ρ ≤ ε := by
    have h : ρ ≤ ε/(A*2000*t) := min_le_right _ _
    simpa only [mul_comm] using (le_div_iff₀ (show 0 < A*2000*t by positivity)).mp h
  have hpoly : (1+ρ)*(1+ρ*e) ≤ 1+t*ρ := by
    have hsq : ρ^2 ≤ ρ := by nlinarith
    have hx := mul_le_mul_of_nonneg_left hsq he.le
    dsimp only [t]
    nlinarith only [hx]
  refine ⟨ρ,hρ,?_⟩
  intro K hK hKhi
  have herr : A*(t*ρ*K) ≤ ε := calc
    _ ≤ A*(t*ρ*2000) := by gcongr
    _ = (A*2000*t)*ρ := by ring
    _ ≤ ε := hpay
  calc
    _ = A*((1+ρ)*(1+ρ*e)*K) := by dsimp [A,e]; ring
    _ ≤ A*((1+t*ρ)*K) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpoly hK) hA.le
    _ = A*K+A*(t*ρ*K) := by ring
    _ ≤ _ := by change _ ≤ A*K+ε; linarith

/-- The auxiliary rho is eliminated, but delta is not sent to zero.
All original source labels, five cutoffs and the literal cap coefficient survive. -/
theorem mother_unit_pair_theta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let K := unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
        unitLogCap21 (1/p.kappa3) (1/p.s)
      let a0 := fun d => wuLocalCutoff N δ d p.S
      let a1 := fun d => wuLocalCutoff N δ d p.kappa1
      let a2 := fun d => wuLocalCutoff N δ d p.kappa2
      let a3 := fun d => wuLocalCutoff N δ d p.kappa3
      let b := fun d => wuLocalCutoff N δ d p.s
      FourPrimeUnit.source N W a0 a1 a2 a3 b word20 +
        FourPrimeUnit.source N W a0 a1 a2 a3 b word21 ≤
        ((2/(1-2*δ))*K + ε) * boxTheta N ((N:ℝ)^(1/2-δ)) W := by
  have he : 0 < ε/2 := by positivity
  obtain ⟨ρ,hρ,hbudget⟩ := rho_budget hδhi he
  obtain ⟨T,hT,hd⟩ := mother_unit_pair_theta_rho k hδ hδhi hρ he
  refine ⟨T,hT,?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hN4 := hT.trans hN
  obtain ⟨ha,haa,hab,hbhi⟩ := parameter_log_cap_bounds hp hs
  have hK := unitLogCap_pair_compact ha haa hab hbhi
  have htheta := omega3_source_theta_lower_singular hN4 hδ hδhi hb
  have hC := (wuSingularSeries_pos N (by omega)).le
  have hm : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hΘ : 0 ≤ boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    apply le_trans _ htheta
    positivity
  have hc := mul_le_mul_of_nonneg_right (hbudget _ hK.1 hK.2) hΘ
  have hd' := hd N hN hn i Δ V hb p hp hs
  dsimp only at hd' hc ⊢
  nlinarith only [hd',hc]

end Wu2008DoubleSieve.HighUnitSieve
