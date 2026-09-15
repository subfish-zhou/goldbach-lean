import SrcBuchstabCheckA
import SrcBuchstabCheckB
import SrcBuchstabCheckC
import SrcBuchstabCheckD

namespace WuSource.SrcBuchstab

open LiLiuPrereqBuchstab

theorem base_certificate (i : ℕ) (hi : i < 20) :
    deficit (baseCoeffs (left i) (coefficients i)) (1 / 20) ≤
      baseCoeffs (left i) (coefficients i) 0 ∧ 0 ≤ coefficients i 6 := by
  interval_cases i
  · exact base_00
  · exact base_01
  · exact base_02
  · exact base_03
  · exact base_04
  · exact base_05
  · exact base_06
  · exact base_07
  · exact base_08
  · exact base_09
  · exact base_10
  · exact base_11
  · exact base_12
  · exact base_13
  · exact base_14
  · exact base_15
  · exact base_16
  · exact base_17
  · exact base_18
  · exact base_19

theorem start_certificate : (1 / 2 : ℝ) ≤ coefficients 20 0 :=
  start_20

theorem join_certificate (i : ℕ) (hi : 20 < i) (hi' : i < 68) :
    poly (coefficients (i - 1)) (1 / 20) ≤ coefficients i 0 := by
  interval_cases i
  · exact join_21
  · exact join_22
  · exact join_23
  · exact join_24
  · exact join_25
  · exact join_26
  · exact join_27
  · exact join_28
  · exact join_29
  · exact join_30
  · exact join_31
  · exact join_32
  · exact join_33
  · exact join_34
  · exact join_35
  · exact join_36
  · exact join_37
  · exact join_38
  · exact join_39
  · exact join_40
  · exact join_41
  · exact join_42
  · exact join_43
  · exact join_44
  · exact join_45
  · exact join_46
  · exact join_47
  · exact join_48
  · exact join_49
  · exact join_50
  · exact join_51
  · exact join_52
  · exact join_53
  · exact join_54
  · exact join_55
  · exact join_56
  · exact join_57
  · exact join_58
  · exact join_59
  · exact join_60
  · exact join_61
  · exact join_62
  · exact join_63
  · exact join_64
  · exact join_65
  · exact join_66
  · exact join_67

theorem step_certificate (i : ℕ) (hi : 20 ≤ i) (hi' : i < 68) :
    deficit (residual (left i) (coefficients i) (coefficients (i - 20))) (1 / 20) ≤
      residual (left i) (coefficients i) (coefficients (i - 20)) 0 := by
  interval_cases i
  · exact step_20
  · exact step_21
  · exact step_22
  · exact step_23
  · exact step_24
  · exact step_25
  · exact step_26
  · exact step_27
  · exact step_28
  · exact step_29
  · exact step_30
  · exact step_31
  · exact step_32
  · exact step_33
  · exact step_34
  · exact step_35
  · exact step_36
  · exact step_37
  · exact step_38
  · exact step_39
  · exact step_40
  · exact step_41
  · exact step_42
  · exact step_43
  · exact step_44
  · exact step_45
  · exact step_46
  · exact step_47
  · exact step_48
  · exact step_49
  · exact step_50
  · exact step_51
  · exact step_52
  · exact step_53
  · exact step_54
  · exact step_55
  · exact step_56
  · exact step_57
  · exact step_58
  · exact step_59
  · exact step_60
  · exact step_61
  · exact step_62
  · exact step_63
  · exact step_64
  · exact step_65
  · exact step_66
  · exact step_67

theorem cap_certificate (i : ℕ) (hi : 48 ≤ i) (hi' : i < 68) (j : Fin 7) :
    bernstein (coefficients i) (1 / 20) j ≤ 561522 / 1000000 := by
  interval_cases i
  · exact cap_48 j
  · exact cap_49 j
  · exact cap_50 j
  · exact cap_51 j
  · exact cap_52 j
  · exact cap_53 j
  · exact cap_54 j
  · exact cap_55 j
  · exact cap_56 j
  · exact cap_57 j
  · exact cap_58 j
  · exact cap_59 j
  · exact cap_60 j
  · exact cap_61 j
  · exact cap_62 j
  · exact cap_63 j
  · exact cap_64 j
  · exact cap_65 j
  · exact cap_66 j
  · exact cap_67 j

theorem fixed_initial_window {t : ℝ}
    (ht : (17 / 5 : ℝ) ≤ t) (ht' : t ≤ 22 / 5) :
    buchstab t ≤ 561522 / 1000000 := by
  obtain ⟨i, hi, hi', hx, hx'⟩ := initial_window_covered ht ht'
  have hb := certified_prefix coefficients base_certificate start_certificate
    join_certificate step_certificate i hi' hx hx'
  have hc := bernstein_cap (by norm_num : (0 : ℝ) < 1 / 20)
    hx hx' (cap_certificate i hi hi')
  have he : left i + (t - left i) = t := by ring
  rw [he] at hb
  exact hb.trans hc

#print axioms fixed_initial_window

end WuSource.SrcBuchstab
