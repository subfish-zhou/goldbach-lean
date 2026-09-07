import PrimeNumberTheoremAnd.Consequences

open Filter Asymptotics

#check pi_alt'
#print axioms pi_alt'

example :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x => x / Real.log x) := pi_alt'