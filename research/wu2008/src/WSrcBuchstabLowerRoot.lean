import BuchstabSeedTightLower

namespace WuSource.SrcBuchstabLower

open LiLiuPrereqBuchstab

theorem buchstab_lower56_seed {u : ℝ} (hu : (3 : ℝ) ≤ u) (hu' : u ≤ 4) :
    (14 / 25 : ℝ) ≤ buchstab u := by
  simpa only [Wu2008DoubleSieve.BuchstabSeedTightLower.lower] using
    Wu2008DoubleSieve.BuchstabSeedTightLower.buchstab_seed_lower hu hu'

theorem buchstab_lower56 :
    ∀ u : ℝ, (3 : ℝ) ≤ u → (14 / 25 : ℝ) ≤ buchstab u := by
  intro u hu
  simpa only [Wu2008DoubleSieve.BuchstabSeedTightLower.lower] using
    Wu2008DoubleSieve.BuchstabSeedTightLower.buchstab_true_lower hu

theorem weighted_buchstab_lower56 {u w : ℝ} (hu : (3 : ℝ) ≤ u) (hw : 0 ≤ w) :
    w * (14 / 25 : ℝ) ≤ w * buchstab u :=
  mul_le_mul_of_nonneg_left (buchstab_lower56 u hu) hw

#check buchstab_lower56_seed
#check buchstab_lower56
#check weighted_buchstab_lower56
#print axioms buchstab_lower56_seed
#print axioms buchstab_lower56
#print axioms weighted_buchstab_lower56

end WuSource.SrcBuchstabLower
