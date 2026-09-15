import W16FiniteExitV3

noncomputable section
namespace WuTarget.W16
open Finset Real
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical

theorem unit_eventually {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → 1 ≤ ε*U8CanonicalMother.M N := by
  have hc : 0 < ε*liuUniversalProduct := mul_pos hε liuUniversalProduct_pos
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp
    (Wu2008DoubleSieve.box_eventually_log_power_budget 2
      (one_div_pos.mpr hc) (by norm_num : (0 : ℝ) < 1))
  refine ⟨max 512 T,le_max_left _ _,fun N hN => ?_⟩
  have hN512 : 512 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN0
  have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb := hT N ((le_max_right _ _).trans hN)
  rw [Real.rpow_one] at hb
  have hb' : log (N : ℝ)^2 / (ε*liuUniversalProduct) ≤ N := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hb
  have hb'' := (div_le_iff₀ hc).mp hb'
  have hs := mul_le_mul_of_nonneg_left
    (liuUniversalProduct_le_liuSingularSeries N) (mul_pos hε hNr).le
  rw [U8CanonicalMother.scale_eq_liu hN0, ← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
  nlinarith only [hb'',hs]

/-- The two bad-set bounds are explicit unpaid analytic inputs, not representation hypotheses. -/
theorem eventual_exit_of_bad_bounds {c : ℝ} (hc : 4491/5000 ≤ c)
    (hcount : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
        ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (c-ε)*U8CanonicalMother.M N ≤ ((ordinaryP2 N).card : ℝ))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧ η ≤ 1/2 ∧
        ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
          ((smallBad N η).card : ℝ) ≤ ε*U8CanonicalMother.M N)
    (hlarge : ∀ η : ℝ, 0 < η → η ≤ 1/2 → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
        ((largeBad N η).card : ℝ) ≤
          (8*log (5000/4469)+ε)*U8CanonicalMother.M N) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ 1/2 ∧
        ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          margin/2*U8CanonicalMother.M N ≤ ((good N).card : ℝ) ∧
            ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
              N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ) ^ (4469/5000 : ℝ) := by
  have he : 0 < margin/8 := div_pos margin_pos (by norm_num)
  obtain ⟨δ,hδ,hδhi,Tc,hTc,hcN⟩ := hcount (margin/8) he
  obtain ⟨η,hη,hηhi,Ts,hsN⟩ := hsmall (margin/8) he
  obtain ⟨Tl,hlN⟩ := hlarge η hη hηhi (margin/8) he
  obtain ⟨Tu,_,huN⟩ := unit_eventually he
  refine ⟨δ,hδ,hδhi,η,hη,hηhi,max Tc (max Ts (max Tl Tu)),by omega,fun N hN heven => ?_⟩
  exact same_N_exit (by omega) hc (by linarith) (hcN N (by omega) heven)
    (hsN N (by omega) heven) (hlN N (by omega) heven) (huN N (by omega))

theorem actual_ordinary_coefficient (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (U8CanonicalMother.improvedCoefficient-ε)*U8CanonicalMother.M N ≤
          ((ordinaryP2 N).card : ℝ) :=
  U8CanonicalMother.improved_ordinary_P2 ε hε

/-- This consumes the frozen actual producer; it does not certify its coefficient or the bad bounds. -/
theorem actual_exit_of_bad_bounds
    (hc : (4491/5000 : ℝ) ≤ U8CanonicalMother.improvedCoefficient)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧ η ≤ 1/2 ∧
        ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
          ((smallBad N η).card : ℝ) ≤ ε*U8CanonicalMother.M N)
    (hlarge : ∀ η : ℝ, 0 < η → η ≤ 1/2 → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
        ((largeBad N η).card : ℝ) ≤
          (8*log (5000/4469)+ε)*U8CanonicalMother.M N) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ 1/2 ∧
        ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          margin/2*U8CanonicalMother.M N ≤ ((good N).card : ℝ) ∧
            ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
              N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ) ^ (4469/5000 : ℝ) :=
  eventual_exit_of_bad_bounds hc actual_ordinary_coefficient hsmall hlarge

end WuTarget.W16
