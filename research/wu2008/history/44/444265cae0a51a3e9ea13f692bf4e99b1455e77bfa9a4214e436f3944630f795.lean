import R2MotherSourceTransport

namespace WuPaper.R2Mother

open Finset Wu2008DoubleSieve
open scoped Classical

theorem no_natural_sqrt_endpoint {N a b : ℕ}
    (ha : a.Prime) (haN : a.Coprime N) (hb : 0 < b) (q : ℕ) :
    (q : ℝ) ≠ Real.sqrt ((N : ℝ) / ((a : ℝ) * b)) := by
  intro hq
  have hab : (0 : ℝ) < (a : ℝ) * b := by
    exact mul_pos (by exact_mod_cast ha.pos) (by exact_mod_cast hb)
  have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg N) hab.le)
  rw [← hq] at hs
  have he : q ^ 2 * (a * b) = N := by
    exact_mod_cast (eq_div_iff hab.ne').mp hs
  have haD : a ∣ q ^ 2 * (a * b) :=
    dvd_mul_of_dvd_right (dvd_mul_right a b) (q ^ 2)
  have ha1 : a ∣ 1 := by
    rw [he] at haD
    simpa only [haN.gcd_eq_one] using Nat.dvd_gcd (dvd_refl a) haD
  exact ha.not_dvd_one ha1

theorem ninth_endpoint_loss_empty {N a b : ℕ}
    (ha : a.Prime) (haN : a.Coprime N) (hb : 0 < b) :
    sieveEndpointLoss N (a * b) (N * a)
      (Real.sqrt ((N : ℝ) / ((a : ℝ) * b))) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨_, _, _, _, q, _, _, hq, _⟩ := mem_sieveEndpointLoss.mp hp
  exact no_natural_sqrt_endpoint ha haN hb q hq

theorem ninth_strict_eq_closed (N : ℕ) (w u : ℝ) :
    upsilon9 N w u =
      ∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
        sieveCountLE N (t.1 * t.2) (N * t.1)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2))) := by
  apply sum_congr rfl
  intro t ht
  obtain ⟨ha, hb, hcop, _⟩ := mem_lowerPairs_source.mp (mem_filter.mp ht).1
  rw [sieveCount_eq_closed_add_loss, ninth_endpoint_loss_empty ha
    (Nat.coprime_mul_iff_left.mp hcop).1 hb.pos]
  simp only [card_empty, Int.natCast_zero, add_zero]

end WuPaper.R2Mother

#check @WuPaper.R2Mother.no_natural_sqrt_endpoint
#check @WuPaper.R2Mother.ninth_endpoint_loss_empty
#check @WuPaper.R2Mother.ninth_strict_eq_closed
#print axioms WuPaper.R2Mother.no_natural_sqrt_endpoint
#print axioms WuPaper.R2Mother.ninth_endpoint_loss_empty
#print axioms WuPaper.R2Mother.ninth_strict_eq_closed
