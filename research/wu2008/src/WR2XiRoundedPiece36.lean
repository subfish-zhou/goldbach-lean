import WR2XiRationalRounded
namespace Xi2RationalMixed
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rounded_piece_3_6 : roundedPiece 3 0 6 = (3897936623/1000000000000 : ℚ) := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.rounded_piece_3_6
