import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedRoughSharp
import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedDivisors
import MathlibNt.SieveTheory.LiLiuGoldbachG11CollarPaid

open Filter
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- All actual grid extensions are now paid: ordered rough mother, ordering
collar and newly admitted ambient prime divisors. The threshold precedes all
changing epsilon, rho and bounded nonnegative weights. -/
theorem goldbachG11WeightedGridMass_le_paidKernel :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε ρ : ℝ, 1 < ρ → ρ ≤ 5/4 →
      ∀ (h : ℝ → ℝ) (H : ℝ), 0 ≤ H → (∀ r,0 ≤ h r) → (∀ r,h r ≤ H) →
      (Real.log (N : ℝ)/N)*goldbachG11WeightedGridMass N ε ρ h ≤
        ρ^2*((561522/1000000 : ℝ)+η)*goldbachG11PrimeKernel h N+
        C*H*(ρ-1)+16800*H*Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ) := by
  obtain ⟨C,hC,Mc,hMc,hc⟩ := goldbachG11Collar_rough_paid
  obtain ⟨B,hB⟩ := eventually_atTop.mp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).eventually
    (eventually_ge_atTop (4 : ℝ)))
  refine ⟨C,hC,?_⟩
  intro η hη
  obtain ⟨Mr,hMr,hr⟩ := goldbachG11ExpandedRoughMass_le_sharpKernel η hη
  refine ⟨max Mr (max Mc ⌈B⌉₊),hMr.trans (le_max_left _ _),?_⟩
  intro N hN ε ρ hρ hρu h H hH hh hhH
  have hn4 : 4 ≤ N := by omega
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hnorm : 0 ≤ Real.log (N : ℝ)/N := div_nonneg hln.le hn0.le
  have hbig := hB N ((Nat.le_ceil B).trans (by exact_mod_cast (show ⌈B⌉₊ ≤ N by omega)))
  have hg := (goldbachG11WeightedGridMass_le_expandedMother (ε := ε) hρ hρu hbig h hh).trans
    (goldbachG11ExpandedMother_split N ρ h hh)
  have ho := mul_le_mul_of_nonneg_left (goldbachG11Expanded_ordered_le_rough N ρ h hh) hnorm
  have ho' := ho.trans (hr N (by omega) ρ hρ.le hρu h hh)
  have hd := mul_le_mul_of_nonneg_left (goldbachG11Expanded_divisor_mass hn4 hρ.le hρu h H hH hhH) hnorm
  have hd' : (Real.log (N : ℝ)/N)*goldbachG11ExpandedMotherSlice N ρ h (fun _ p => p ∣ N) ≤
      16800*H*Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ) := hd.trans_eq (by field_simp)
  have hcoll := mul_le_mul_of_nonneg_left (goldbachG11Expanded_collar_le_rough N ρ h H hH hhH) hnorm
  have hcoll' : (Real.log (N : ℝ)/N)*goldbachG11ExpandedMotherSlice N ρ h (fun m p => m.minFac < p) ≤
      C*H*(ρ-1) := by
    calc
      _ ≤ (Real.log (N : ℝ)/N)*(H*goldbachG11CollarRoughMass N ρ) := hcoll
      _ = H*((Real.log (N : ℝ)/N)*goldbachG11CollarRoughMass N ρ) := by ring
      _ ≤ H*(C*(ρ-1)) := mul_le_mul_of_nonneg_left (hc N (by omega) ρ hρ.le hρu) hH
      _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_left hg hnorm
  rw [mul_add,mul_add] at hs
  exact hs.trans ((add_le_add (add_le_add ho' hd') hcoll').trans_eq (by ring))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig