import WR2XiRationalRounded
namespace Xi2RationalMixed
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rounded_piece_1_8 : roundedPiece 1 0 8 = (43374209809/1000000000000 : ℚ) := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.rounded_piece_1_8
