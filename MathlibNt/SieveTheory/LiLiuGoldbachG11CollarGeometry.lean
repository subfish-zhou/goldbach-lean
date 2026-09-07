import MathlibNt.SieveTheory.LiLiuGoldbachG11CollarTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedRoughUniform

open Finset LiLiuPrereqBuchstab
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The same rho that enlarges the short-prime endpoint also enlarges the
product endpoint by rho^2. Hence no extra loss is needed for the lower cofactor. -/
theorem goldbachG11Collar_cofactor_geometry {N : ℕ} (hN : 4 ≤ N) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (hρu : ρ ≤ 5/4) {v : GoldbachG11SwitchedBody}
    (hv : v ∈ goldbachG11CollarBoxes N ρ) :
    let y := ρ^2*N/goldbachG11SwitchedBodyProd v
    (N : ℝ)^(1/2 : ℝ) ≤ y ∧ y ≤ (N : ℝ)^2 ∧
      (N : ℝ)^(4/53 : ℝ) ≤ (v.2.2.1 : ℝ) ∧ (v.2.2.1 : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) ∧
      0 < goldbachG11SwitchedBodyProd v ∧ v.2.2.1.Prime := by
  rcases v with ⟨t,s,q,p⟩
  obtain ⟨ht,hs,hq,hp⟩ :
      t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      q ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      p ∈ Ioc q ⌊ρ*(q : ℝ)⌋₊ := by simpa only [goldbachG11CollarBoxes,mem_sigma] using hv
  obtain ⟨htP,_htN,_hzt,htb⟩ := mem_goldbachClosedPrimes_iff.mp ht
  obtain ⟨hsP,_hsN,_hzs,hsb⟩ := mem_goldbachClosedPrimes_iff.mp hs
  obtain ⟨hqP,_hqN,hzq,hqb⟩ := mem_goldbachClosedPrimes_iff.mp hq
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hρ0 : 0 ≤ ρ := by linarith
  have hp0 : 0 < p := hqP.pos.trans (mem_Ioc.mp hp).1
  have hpρ : (p : ℝ) ≤ ρ*q := (Nat.cast_le.mpr (mem_Ioc.mp hp).2).trans (Nat.floor_le (by positivity))
  have hpb : (p : ℝ) ≤ ρ*(N : ℝ)^(4/33 : ℝ) := hpρ.trans (mul_le_mul_of_nonneg_left hqb hρ0)
  have hdN : 0 < goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ := by
    dsimp [goldbachG11SwitchedBodyProd]
    exact mul_pos (mul_pos (mul_pos hqP.pos hsP.pos) htP.pos) hp0
  have hd0 : (0 : ℝ) < goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ := by exact_mod_cast hdN
  have hd1 : (1 : ℝ) ≤ goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ := by exact_mod_cast hdN
  have hdB : (goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ : ℝ) ≤ ρ*(N : ℝ)^(16/33 : ℝ) := by
    have hpow : ((N : ℝ)^(4/33 : ℝ))^4 = (N : ℝ)^(16/33 : ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
      norm_num
    calc
      _ ≤ (N : ℝ)^(4/33 : ℝ)*(N : ℝ)^(4/33 : ℝ)*(N : ℝ)^(4/33 : ℝ)*(ρ*(N : ℝ)^(4/33 : ℝ)) := by
        simp only [goldbachG11SwitchedBodyProd,Nat.cast_mul]
        gcongr
      _ = ρ*((N : ℝ)^(4/33 : ℝ))^4 := by ring
      _ = _ := by rw [hpow]
  have hlower : (N : ℝ)^(17/33 : ℝ) ≤ ρ^2*N/goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ := by
    apply (le_div_iff₀ hd0).2
    calc
      _ ≤ (N : ℝ)^(17/33 : ℝ)*(ρ*(N : ℝ)^(16/33 : ℝ)) := mul_le_mul_of_nonneg_left hdB (by positivity)
      _ = ρ*(N : ℝ) := by
        rw [mul_left_comm,← Real.rpow_add hn0]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith : ρ ≤ ρ^2) hn0.le
  have hρ2 : ρ^2 ≤ (2 : ℝ) := by nlinarith
  have hupper : ρ^2*N/goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ ≤ (N : ℝ)^2 := by
    calc
      _ ≤ ρ^2*N := div_le_self (by positivity) hd1
      _ ≤ 2*(N : ℝ) := mul_le_mul_of_nonneg_right hρ2 hn0.le
      _ ≤ _ := by
        have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
  exact ⟨(Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/2 : ℝ) ≤ 17/33)).trans hlower,
    hupper,hzq,hqb,hdN,hqP⟩

/-- A fixed coarse rough-count budget for the ordering collar, uniform in rho. -/
theorem goldbachG11Collar_rough_point_bound :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 5/4 →
      ∀ v ∈ goldbachG11CollarBoxes N ρ,
        (Real.log (N : ℝ)/N)*(roughCount (ρ^2*N/goldbachG11SwitchedBodyProd v) v.2.2.1 : ℝ) ≤
          53*(1/(goldbachG11SwitchedBodyProd v : ℝ)) := by
  obtain ⟨M,hM,hm⟩ := goldbachG11_expanded_rough_coarse 1 (by norm_num)
  refine ⟨M,hM,?_⟩
  intro N hN ρ hρ hρu v hv
  have hn4 := hM.trans hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨hyl,hyu,hql,hqu,hd,hqP⟩ := goldbachG11Collar_cofactor_geometry hn4 hρ hρu hv
  have hr := hm N hN v.2.2.1 (ρ^2*N/goldbachG11SwitchedBodyProd v) hql hqu hyl hyu
  have hlq : 0 < Real.log (v.2.2.1 : ℝ) := Real.log_pos (by exact_mod_cast hqP.one_lt)
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hql
  rw [Real.log_rpow hn0] at hl
  have hlratio : Real.log (N : ℝ)/Real.log (v.2.2.1 : ℝ) ≤ (53/4 : ℝ) := by
    apply (div_le_iff₀ hlq).2
    linarith
  have hρ2 : ρ^2 ≤ (2 : ℝ) := by nlinarith
  have hscalar : 2*ρ^2*(Real.log (N : ℝ)/Real.log (v.2.2.1 : ℝ)) ≤ 53 := by
    calc
      _ ≤ 2*2*(53/4 : ℝ) := by gcongr
      _ = _ := by norm_num
  calc
    _ ≤ (Real.log (N : ℝ)/N)*((1+1)*(ρ^2*N/goldbachG11SwitchedBodyProd v)/Real.log (v.2.2.1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hr (div_nonneg hln.le hn0.le)
    _ = (2*ρ^2*(Real.log (N : ℝ)/Real.log (v.2.2.1 : ℝ)))*(1/(goldbachG11SwitchedBodyProd v : ℝ)) := by field_simp; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hscalar (by positivity)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig