import MathlibNt.Wu2008DoubleSieve.GeoMassSelectedFibresFubini

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
open Set MeasureTheory
open scoped BigOperators

/-- Genuine selected-coordinate Fubini with the two literal ordered integrals. -/
theorem selectedOrderedMass_fibre {n : ℕ} (j : Fin n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    selectedOrderedMass j a b =
      ∫ t in a..b, pureOrderedMass j.val a t *
        pureOrderedMass (n-1-j.val) t b / t^2 := by
  rcases j with ⟨m,hm⟩
  obtain ⟨k,hk⟩ : ∃ k, n = m+(k+1) := ⟨n-1-m, by omega⟩
  subst n
  have hj : (⟨m,hm⟩ : Fin (m+(k+1))) = Fin.natAdd m (0 : Fin (k+1)) := by
    apply Fin.ext
    simp
  have hd : m+(k+1)-1-m = k := by omega
  simpa only [Fin.val_mk, hd, hj] using selectedOrderedMass_fibre_add m k ha hab

theorem selectedOrderedMass_same {n : ℕ} (j : Fin n) {a : ℝ} (ha : 0 < a) :
    selectedOrderedMass j a a = 0 := by
  rw [selectedOrderedMass_fibre j ha le_rfl]
  simp

theorem selectedOrderedMass_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    selectedOrderedMass (0 : Fin 1) a b = ∫ t in a..b, 1 / t^2 := by
  rw [selectedOrderedMass_fibre _ ha hab]
  simp only [Fin.val_zero, Nat.sub_self, pure_zero, mul_one]

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
