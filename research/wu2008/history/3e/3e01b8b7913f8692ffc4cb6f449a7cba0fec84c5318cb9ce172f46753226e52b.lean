import SrcBuchstabCertificate

namespace WuSource.SrcBuchstab

open LiLiuPrereqBuchstab

theorem buchstab_le_source_fine {t : ℝ} (ht : (17 / 5 : ℝ) ≤ t) :
    buchstab t ≤ 561522 / 1000000 :=
  fine_tail_of_initial_window (fun _ ha hb => fixed_initial_window ha hb) ht

theorem buchstab_le_weak_fine {t : ℝ} (ht : (17 / 5 : ℝ) ≤ t) :
    buchstab t ≤ 5616 / 10000 :=
  (buchstab_le_source_fine ht).trans (by norm_num)

theorem buchstab_le_on_wu04_domain {t : ℝ} (ht : (7 / 2 : ℝ) ≤ t) :
    buchstab t ≤ 561522 / 1000000 :=
  buchstab_le_source_fine (by linarith)

theorem weighted_buchstab_le_source_fine {t w : ℝ}
    (ht : (17 / 5 : ℝ) ≤ t) (hw : 0 ≤ w) :
    w * buchstab t ≤ w * (561522 / 1000000) :=
  mul_le_mul_of_nonneg_left (buchstab_le_source_fine ht) hw

theorem fine_cap_saving :
    (4 / 7 : ℝ) - 561522 / 1000000 = 34673 / 3500000 := by norm_num

#check buchstab_le_source_fine
#check buchstab_le_weak_fine
#check buchstab_le_on_wu04_domain
#check weighted_buchstab_le_source_fine
#check fine_cap_saving
#print axioms buchstab_le_source_fine
#print axioms buchstab_le_weak_fine
#print axioms buchstab_le_on_wu04_domain
#print axioms weighted_buchstab_le_source_fine
#print axioms fine_cap_saving

end WuSource.SrcBuchstab
