import MathlibNt.SieveTheory.LiLiuGoldbachG11CofactorWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughSandwich

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The three selected factors and the remaining rough cofactor form an ordinary rough body.
This is independent of the Goldbach prime-output condition. -/
theorem goldbachG11_body_survives {q s t k : ℕ}
    (hq : q.Prime) (hs : s.Prime) (ht : t.Prime)
    (hqs : q ≤ s) (hst : s ≤ t) (hk : SurvivesSieve 1 q k) :
    SurvivesSieve 1 q (q * s * t * k) := by
  simpa only [one_mul] using
    (goldbachG11_rough_mul_survives (N := 1) (r := 1) hq hs ht hqs hst hk)

/-- Even with repeated selected primes, the second original prime is determined by the
switched product itself. This does not identify the remaining two labels. -/
theorem goldbachG11_body_minFac {q s t k : ℕ}
    (hq : q.Prime) (hs : s.Prime) (ht : t.Prime)
    (hqs : q ≤ s) (hst : s ≤ t) (hk : SurvivesSieve 1 q k) :
    (q * s * t * k).minFac = q := by
  have hd : q ∣ q * s * t * k :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right q s) t) k
  have hne : q * s * t * k ≠ 1 := by
    intro heq
    exact hq.not_dvd_one (heq ▸ hd)
  have hr := (goldbachG11_rough_iff_survives (q : ℝ) (q * s * t * k)).mpr
    (goldbachG11_body_survives hq hs ht hqs hst hk)
  have hlo : q ≤ (q * s * t * k).minFac := by
    exact_mod_cast (LiLiuPrereqBuchstab.rough_iff_minFac hne).mp hr
  exact le_antisymm (Nat.minFac_le_of_dvd hq.two_le hd) hlo

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig