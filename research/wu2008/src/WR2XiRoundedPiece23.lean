import WR2XiRationalRounded
namespace Xi2RationalMixed
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rounded_piece_2_3 : roundedPiece 2 0 3 = (17299180216/1000000000000 : ℚ) := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.rounded_piece_2_3
