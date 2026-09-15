import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighKernelPayloads

namespace Wu2008DoubleSieve.HighSourcePayload
open HighUnit HighUnitSource Real

/-- Nonnegativity holds at the actual common phi, with no source-box restriction. -/
theorem unitPair_nonneg (N d : ℕ) (δ : ℝ) {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) : 0 ≤ unitPair N d δ p := by
  obtain ⟨ha, haa, hab, hb⟩ := parameter_log_cap_bounds hp hs
  exact add_nonneg (J20_nonneg ha haa hab hb _) (J21_nonneg (ha.trans haa) hb _)

/-- Two-sided quadrature of the actual unfiltered X, retaining the shared J mass. -/
theorem mother_boxed_pair_mass (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      |boxedSigma20 N δ W (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
        boxedSigma21 N δ W (fun _ => 1/p.kappa3) (fun _ => 1/p.s) -
        mass N δ Δ V (fun d => unitPair N d δ p)| ≤
      ε * ((N:ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T, hT4, hT⟩ := boxed_sigma_pair_combined k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  rw [unit_mass_eq_boxed]
  exact (hT N hN i Δ V hb _ _ _ (fun _ _ => parameter_outer_bounds hp hs)).2.2

/-- A universal compact cap for the genuine J pair; only an error-budget bound. -/
theorem unitPair_bounds (N d : ℕ) (δ : ℝ) {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    0 ≤ unitPair N d δ p ∧ unitPair N d δ p ≤ 2000 := by
  obtain ⟨ha, haa, hab, hb⟩ := parameter_log_cap_bounds hp hs
  refine ⟨unitPair_nonneg N d δ hp hs, ?_⟩
  have hcap := add_le_add (J20_log_cap ha haa hab hb (omega3XPhi N d δ))
    (J21_log_cap (ha.trans haa) hab hb (omega3XPhi N d δ))
  exact hcap.trans (unitLogCap_pair_compact ha haa hab hb).2

/-- Original prime-output physical source to the unchanged same-phi J mass.
The full rho/delta density survives, and C(N) is paid only on the quadrature error. -/
theorem mother_unit_pair_J_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let a0 := fun d => wuLocalCutoff N δ d p.S
      let a1 := fun d => wuLocalCutoff N δ d p.kappa1
      let a2 := fun d => wuLocalCutoff N δ d p.kappa2
      let a3 := fun d => wuLocalCutoff N δ d p.kappa3
      let b := fun d => wuLocalCutoff N δ d p.s
      FourPrimeUnit.source N W a0 a1 a2 a3 b word20 +
        FourPrimeUnit.source N W a0 a1 a2 a3 b word21 ≤
      ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
        wuSingularSeries N / log N * mass N δ Δ V (fun d => unitPair N d δ p) +
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) W := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hden : 0 < 1-2*δ := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 0 < A+1 := by linarith
  have htol : 0 < ε/(A+1) := div_pos hε hA1
  obtain ⟨T1,hT14,hT1⟩ := HighUnitSieve.mother_unit_pair_density k hδ hδhi hρ (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := mother_boxed_pair_mass k hδ hδhi htol
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb p hp hs
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  let W := convolutionWuWindows N Δ V
  let X := boxedSigma20 N δ W (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
    boxedSigma21 N δ W (fun _ => 1/p.kappa3) (fun _ => 1/p.s)
  let M := mass N δ Δ V (fun d => unitPair N d δ p)
  let E := ((N:ℝ) / log N) * boxConvolutionReciprocalMass W
  let C := wuSingularSeries N / log N
  let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) W
  have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ C := div_nonneg (wuSingularSeries_pos N (by omega)).le hlog.le
  have hrec : 0 ≤ boxConvolutionReciprocalMass W :=
    Finset.sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hE : 0 ≤ E := mul_nonneg (div_nonneg (Nat.cast_nonneg _) hlog.le) hrec
  have hpay : C * E ≤ Θ/2 := by
    simpa only [C, E, Θ, W, mul_assoc] using reciprocalMass_theta_payment hN4 hδ hδhi hb
  have hΘ : 0 ≤ Θ := by linarith [mul_nonneg hC hE]
  have hbudget : A*(ε/(A+1)) ≤ ε := by
    have hid := div_mul_cancel₀ ε (ne_of_gt hA1)
    nlinarith only [hid, htol.le]
  have hquad := (le_abs_self _).trans (hT2 N hN2 i Δ V hb p hp hs)
  change X - M ≤ ε/(A+1) * ((N:ℝ)/log N) * boxConvolutionReciprocalMass W at hquad
  have hquad' : X ≤ M + (ε/(A+1))*E := by dsimp [E]; linarith only [hquad]
  have hsource := hT1 N hN1 heven i Δ V hb p hp hs
  dsimp only at hsource ⊢
  simp only [mul_div_assoc] at hsource ⊢
  change _ ≤ X*(A*C) + (ε/2)*Θ at hsource
  change _ ≤ A*C*M + ε*Θ
  calc
    _ ≤ X*(A*C) + (ε/2)*Θ := hsource
    _ ≤ (M + (ε/(A+1))*E)*(A*C) + (ε/2)*Θ :=
      add_le_add (mul_le_mul_of_nonneg_right hquad' (mul_nonneg hA hC)) le_rfl
    _ = A*C*M + (A*(ε/(A+1)))*(C*E) + (ε/2)*Θ := by ring
    _ ≤ A*C*M + (A*(ε/(A+1)))*(Θ/2) + (ε/2)*Θ :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hpay (mul_nonneg hA htol.le))) le_rfl
    _ ≤ A*C*M + ε*(Θ/2) + (ε/2)*Θ :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hbudget
          (show (0:ℝ) ≤ Θ/2 from div_nonneg hΘ (by norm_num)))) le_rfl
    _ = _ := by ring

end Wu2008DoubleSieve.HighSourcePayload
