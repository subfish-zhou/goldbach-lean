import Wu08RecoveryMass

noncomputable section
open Finset Real Set LiLiuPrereqBuchstab
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.SmallBoundaryRecovery
open FourRoughClosedMass SmallGrid SmallBoundary

/-- One symbolic tolerance pays all already established kernel and strip costs.
The rational constants below are only bounds, not a numerical parameter search. -/
theorem buchstabGrid_integral_paid {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ ε τ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < τ ∧
      ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) → ∀ e : Bool, ∀ ρ : ℝ,
        1 < ρ → ρ ≤ 5/4 → buchstabGrid N e ρ ε τ ≤ SmallQuadrature.I e+ζ := by
  have ha : 0 < (FourRoughClosedMass.alpha-1/15)/2 := by
    norm_num [FourRoughClosedMass.alpha,truncatedSixthLowerAlpha]
  have hb : 0 < FourRoughClosedMass.beta-1/10 := by
    norm_num [FourRoughClosedMass.beta,truncatedSixthLowerBeta]
  have hc : 0 < ((1/3 : ℝ)-lam+FourRoughClosedMass.alpha)/2 := by
    norm_num [lam,FourRoughClosedMass.alpha,truncatedSixthLowerAlpha,truncatedSixthLowerLambda]
  obtain ⟨t,ht,htu⟩ := exists_between (lt_min (by norm_num : (0 : ℝ) < 1)
    (lt_min ha (lt_min hb (lt_min hc (show 0 < ζ/3000000 by positivity)))))
  have ht1 : t ≤ 1 := (htu.trans_le (min_le_left _ _)).le
  have hta : t < (FourRoughClosedMass.alpha-1/15)/2 :=
    htu.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htb : t < FourRoughClosedMass.beta-1/10 :=
    htu.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htc : t < ((1/3 : ℝ)-lam+FourRoughClosedMass.alpha)/2 :=
    htu.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have htz : t < ζ/3000000 :=
    htu.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hlo : 2*t ≤ FourRoughClosedMass.alpha-1/15 := by linarith
  have hhi : 1/10+t ≤ FourRoughClosedMass.beta := by linarith
  have htop : lam-FourRoughClosedMass.alpha+2*t ≤ 1/3 := by linarith
  obtain ⟨T1,hT1,h1⟩ := unshiftedMass_I_paid ht.le ht hlo hhi htop
  obtain ⟨T2,_,h2⟩ := windowMass_uniform
  obtain ⟨T3,_,h3⟩ := log_shift_uniform ht
  refine ⟨t,t,ht,ht1,ht,max (T1 : ℝ) (max (T2 : ℝ) T3),?_,?_⟩
  · exact (show (4 : ℝ) ≤ T1 by exact_mod_cast hT1).trans (le_max_left _ _)
  intro N hN e ρ hρ hρu
  have hN1 : T1 ≤ N := by exact_mod_cast ((le_max_left _ _).trans hN)
  have hN2 : T2 ≤ N := by exact_mod_cast ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : T3 ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast (hT1.trans hN1)
  have hs := (h3 N hN3 ρ hρ hρu).2
  have hu := h1 N hN1 e ρ hρ hs
  have hg := buchstabGrid_shift_paid (e := e) hn4 hρ hρu hs hlo hhi htop ht.le ht1 ht.le (h2 N hN2)
  linarith only [hu,hg,htz,ht]

/-- Symbolically choose a physical dilation. The integral is not numerically
sampled or assumed positive; absolute values give a uniform two-domain bound. -/
theorem choose_dilation {σ : ℝ} (hσ : 0 < σ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 5/4 ∧ ∀ e : Bool,
      ρ*(SmallQuadrature.I e+σ/4) ≤ SmallQuadrature.I e+σ := by
  let M := |SmallQuadrature.I false|+|SmallQuadrature.I true|+1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨t,ht,htu⟩ := exists_between (lt_min (by norm_num : (0 : ℝ) < 1/4)
    (show 0 < σ/(4*M) by positivity))
  have ht1 : t < 1/4 := htu.trans_le (min_le_left _ _)
  have htm : t*M < σ/4 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*M)).mp (htu.trans_le (min_le_right _ _))
    nlinarith only [hh]
  refine ⟨1+t,by linarith,by linarith,?_⟩
  intro e
  have he : SmallQuadrature.I e ≤ M := by
    cases e
    · dsimp [M]; linarith [le_abs_self (SmallQuadrature.I false),abs_nonneg (SmallQuadrature.I true)]
    · dsimp [M]; linarith [le_abs_self (SmallQuadrature.I true),abs_nonneg (SmallQuadrature.I false)]
  have hmul := mul_le_mul_of_nonneg_left he ht.le
  have hsig := mul_le_mul_of_nonneg_right ht1.le (show 0 ≤ σ/4 by positivity)
  nlinarith only [htm,hmul,hsig,hσ]

/-- First actual small-count terminal, consuming the frozen properMain theorem.
The chosen parameters and threshold work simultaneously for both Bool domains. -/
theorem properMain_integral_paid {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ η ρ : ℝ, 0 < δ ∧ δ < 1/4 ∧ 0 < η ∧ η < 1/8 ∧ 1 < ρ ∧ ρ ≤ 5/4 ∧
      ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) → Even N →
        ∀ e : Bool, ∀ ξ : ℝ, 0 < ξ →
          Normalization.properMain N e ξ ρ δ η ≤
            (SmallQuadrature.I e+σ)*(wuSingularSeries N*N/log N^2) := by
  obtain ⟨ε,τ,hε,_,hτ,Tg,hTg,hg⟩ := buchstabGrid_integral_paid (show 0 < σ/4 by positivity)
  obtain ⟨δ,η,hδ,hδu,hη,hηu,Tp,hp⟩ := properMain_buchstab hε hτ
  obtain ⟨ρ,hρ,hρu,hr⟩ := choose_dilation hσ
  refine ⟨δ,η,ρ,hδ,hδu,hη,hηu,hρ,hρu,max Tg Tp,hTg.trans (le_max_left _ _),?_⟩
  intro N hN he e ξ hξ
  have hNg := (le_max_left _ _).trans hN
  have hn4 := hTg.trans hNg
  have hs : 0 ≤ wuSingularSeries N*N/log N^2 := by
    rw [wuSingularSeries_eq_liu N (by exact_mod_cast (show (0 : ℝ) < N by linarith))]
    exact div_nonneg (mul_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _)) (sq_nonneg _)
  have hgrid := mul_le_mul_of_nonneg_left (hg N hNg e ρ hρ hρu) (by linarith : 0 ≤ ρ)
  have hh := hp N ((le_max_right _ _).trans hN) he e ξ ρ hξ hρ hρu
  exact hh.trans ((mul_le_mul_of_nonneg_left (hgrid.trans (hr e)) hs).trans_eq (mul_comm _ _))

#check buchstabGrid_integral_paid
#print axioms buchstabGrid_integral_paid
#check choose_dilation
#print axioms choose_dilation
#check properMain_integral_paid
#print axioms properMain_integral_paid
end Wu08FirstPrimeFour.SmallBoundaryRecovery
