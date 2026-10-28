import MathlibNt.SieveTheory.Switching.PrimePenaltyAsymptotics

/-!
# Chen's switching and weighted-counting interface

The retained modules provide corrected representation counts, finite weights,
source sieves and varying-prime asymptotics in the
`MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
The actual triple estimate is supplied by `Selberg.Liu.LiuSelbergCorrectedChenBridge`;
`Chen.ChenVerifiedPrerequisites` combines it with the weighted lower bound and
obtains existence from the positive representation count.
-/
