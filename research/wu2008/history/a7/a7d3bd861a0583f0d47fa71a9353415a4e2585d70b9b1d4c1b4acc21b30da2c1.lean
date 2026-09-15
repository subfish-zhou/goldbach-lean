import W08KernelMatrix
import W08Entries0
import W08EntriesRest
import W08Envelope
import W08FrozenConsumer
import W08CellCertificate
import W08Audit

namespace WuTarget.W08

#check @elementaryMatrix_lt_paidMatrix
#check @paidMatrix_le
#check @paidMatrix_apply_eq
#check @paidCells_le_kernel
#check @apply_comparison
#check @apply_strict
#check @v8_actual_consumer
#print axioms elementaryMatrix_lt_paidMatrix
#print axioms paidMatrix_le
#print axioms v8_actual_consumer

end WuTarget.W08
