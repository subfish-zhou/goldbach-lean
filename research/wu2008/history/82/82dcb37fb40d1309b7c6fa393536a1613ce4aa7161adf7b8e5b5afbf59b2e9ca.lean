import E10MajorData

namespace WuTarget.E10Major

set_option pp.fullNames true in
#check @WuTarget.E10Major.fixed_geometry_major
set_option pp.fullNames true in
#check @WuTarget.E10Major.slope_pos
set_option pp.fullNames true in
#check @WuTarget.E10Major.crossCap_pos
set_option pp.fullNames true in
#check @WuTarget.E10Major.recipCoeff_pos
set_option pp.fullNames true in
#check @WuTarget.E10Major.pairCap_lt_target

#print axioms WuTarget.E10Major.fixed_geometry_major
#print axioms WuTarget.E10Major.slope_pos
#print axioms WuTarget.E10Major.crossCap_pos
#print axioms WuTarget.E10Major.recipCoeff_pos
#print axioms WuTarget.E10Major.pairCap_lt_target

end WuTarget.E10Major
