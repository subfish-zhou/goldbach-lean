import SrcFourEnclosureCheckA
import SrcFourEnclosureCheckB
import SrcFourEnclosureCheckC
import SrcFourEnclosureCheckD
import SrcFourEnclosureCheckE
import SrcFourEnclosureCheckF
import SrcFourEnclosureCheckG
import SrcFourEnclosureCheckH

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
namespace WuSource.SrcFourEnclosure

theorem small_certificate (i : ℕ) (hi : i < 64) :
    smallLower i ≤ smallLo (midpoint alpha cut i) ∧
      smallHi (midpoint alpha cut i) ≤ smallUpper i := by
  interval_cases i
  · exact cell_small_00
  · exact cell_small_01
  · exact cell_small_02
  · exact cell_small_03
  · exact cell_small_04
  · exact cell_small_05
  · exact cell_small_06
  · exact cell_small_07
  · exact cell_small_08
  · exact cell_small_09
  · exact cell_small_10
  · exact cell_small_11
  · exact cell_small_12
  · exact cell_small_13
  · exact cell_small_14
  · exact cell_small_15
  · exact cell_small_16
  · exact cell_small_17
  · exact cell_small_18
  · exact cell_small_19
  · exact cell_small_20
  · exact cell_small_21
  · exact cell_small_22
  · exact cell_small_23
  · exact cell_small_24
  · exact cell_small_25
  · exact cell_small_26
  · exact cell_small_27
  · exact cell_small_28
  · exact cell_small_29
  · exact cell_small_30
  · exact cell_small_31
  · exact cell_small_32
  · exact cell_small_33
  · exact cell_small_34
  · exact cell_small_35
  · exact cell_small_36
  · exact cell_small_37
  · exact cell_small_38
  · exact cell_small_39
  · exact cell_small_40
  · exact cell_small_41
  · exact cell_small_42
  · exact cell_small_43
  · exact cell_small_44
  · exact cell_small_45
  · exact cell_small_46
  · exact cell_small_47
  · exact cell_small_48
  · exact cell_small_49
  · exact cell_small_50
  · exact cell_small_51
  · exact cell_small_52
  · exact cell_small_53
  · exact cell_small_54
  · exact cell_small_55
  · exact cell_small_56
  · exact cell_small_57
  · exact cell_small_58
  · exact cell_small_59
  · exact cell_small_60
  · exact cell_small_61
  · exact cell_small_62
  · exact cell_small_63

theorem large_certificate (i : ℕ) (hi : i < 64) :
    largeLower i ≤ largeLo (midpoint cut beta i) ∧
      largeHi (midpoint cut beta i) ≤ largeUpper i := by
  interval_cases i
  · exact cell_large_00
  · exact cell_large_01
  · exact cell_large_02
  · exact cell_large_03
  · exact cell_large_04
  · exact cell_large_05
  · exact cell_large_06
  · exact cell_large_07
  · exact cell_large_08
  · exact cell_large_09
  · exact cell_large_10
  · exact cell_large_11
  · exact cell_large_12
  · exact cell_large_13
  · exact cell_large_14
  · exact cell_large_15
  · exact cell_large_16
  · exact cell_large_17
  · exact cell_large_18
  · exact cell_large_19
  · exact cell_large_20
  · exact cell_large_21
  · exact cell_large_22
  · exact cell_large_23
  · exact cell_large_24
  · exact cell_large_25
  · exact cell_large_26
  · exact cell_large_27
  · exact cell_large_28
  · exact cell_large_29
  · exact cell_large_30
  · exact cell_large_31
  · exact cell_large_32
  · exact cell_large_33
  · exact cell_large_34
  · exact cell_large_35
  · exact cell_large_36
  · exact cell_large_37
  · exact cell_large_38
  · exact cell_large_39
  · exact cell_large_40
  · exact cell_large_41
  · exact cell_large_42
  · exact cell_large_43
  · exact cell_large_44
  · exact cell_large_45
  · exact cell_large_46
  · exact cell_large_47
  · exact cell_large_48
  · exact cell_large_49
  · exact cell_large_50
  · exact cell_large_51
  · exact cell_large_52
  · exact cell_large_53
  · exact cell_large_54
  · exact cell_large_55
  · exact cell_large_56
  · exact cell_large_57
  · exact cell_large_58
  · exact cell_large_59
  · exact cell_large_60
  · exact cell_large_61
  · exact cell_large_62
  · exact cell_large_63

end WuSource.SrcFourEnclosure
