import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT

open Filter Asymptotics

#check pi_alt'
#print axioms pi_alt'

#check LiLiuPrereqBuchstab.primePi_asymptotic
#check LiLiuPrereqBuchstab.tendsto_primeRelativeError
#check LiLiuPrereqBuchstab.primeErrorStart_spec
#check LiLiuPrereqBuchstab.primeRelativeError_le_envelope
#check LiLiuPrereqBuchstab.primeErrorEnvelope_nonneg
#check LiLiuPrereqBuchstab.primeErrorEnvelope_le_one
#check LiLiuPrereqBuchstab.antitone_primeErrorEnvelope
#check LiLiuPrereqBuchstab.tendsto_primeErrorEnvelope
#check LiLiuPrereqBuchstab.primePi_error_le
#check LiLiuPrereqBuchstab.primePi_le_two_mul
#check LiLiuPrereqBuchstab.div_log_mono
#print axioms LiLiuPrereqBuchstab.primePi_asymptotic
#print axioms LiLiuPrereqBuchstab.tendsto_primeRelativeError
#print axioms LiLiuPrereqBuchstab.primeErrorStart_spec
#print axioms LiLiuPrereqBuchstab.primeRelativeError_le_envelope
#print axioms LiLiuPrereqBuchstab.primeErrorEnvelope_nonneg
#print axioms LiLiuPrereqBuchstab.primeErrorEnvelope_le_one
#print axioms LiLiuPrereqBuchstab.antitone_primeErrorEnvelope
#print axioms LiLiuPrereqBuchstab.tendsto_primeErrorEnvelope
#print axioms LiLiuPrereqBuchstab.primePi_error_le
#print axioms LiLiuPrereqBuchstab.primePi_le_two_mul
#print axioms LiLiuPrereqBuchstab.div_log_mono

example :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x => x / Real.log x) := pi_alt'