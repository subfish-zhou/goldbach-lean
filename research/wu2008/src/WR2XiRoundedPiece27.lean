import WR2XiRationalRounded
namespace Xi2RationalMixed
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rounded_piece_2_7 : roundedPiece 2 0 7 = (6320308456/1000000000000 : ℚ) := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.rounded_piece_2_7
