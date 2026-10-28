import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.Compact

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


-- to replace existing `isLittleO_const_id_atTop`


-- to replace existing `isLittleO_const_id_atBot`


theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics
