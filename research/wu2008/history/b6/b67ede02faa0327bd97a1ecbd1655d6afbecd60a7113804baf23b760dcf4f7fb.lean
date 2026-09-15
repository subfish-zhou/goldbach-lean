import MathlibNt.Wu2008DoubleSieve.OmegaTerms

/-!
# Literal quotient labels for the strict Omega3 switching

The selected primes retain their order and the quotient is positive. The
strengthened exclusions do not forbid either selected prime from repeating
in the quotient. Wu04, (5.3)--(5.4), with the strict upper endpoint retained.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def omega3Quotient (N d p1 p2 p3 ell : ℕ) : ℕ :=
  (N - ell) / (d * p1 * p2 * p3)

def omega3Cofactor (d p1 p2 n : ℕ) : ℕ := d * n * p1 * p2

def Omega3Strengthened (N d p1 p2 n : ℕ) : Prop :=
  (p1 * p2).Coprime (d * N) ∧ n.Coprime (d * N) ∧
    ∀ q : ℕ, q.Prime → (q : ℝ) < p2 → q ≠ p1 → ¬q ∣ n

def Omega3BadD (N d ell : ℕ) : Prop := ¬d.Coprime ((N - ell) / d)

theorem omega3_prime_output_lt {N ell : ℕ} (hN : 4 ≤ N) (heven : Even N)
    (hell : ell.Prime) (hellN : ell ≤ N) : ell < N := by
  have hnp : ¬N.Prime := by
    intro hp
    have h2 : 2 ∣ N := even_iff_two_dvd.mp heven
    have : N = 2 := (Nat.dvd_prime hp).mp h2 |>.resolve_left (by decide) |>.symm
    omega
  exact lt_of_le_of_ne hellN (fun h => hnp (h ▸ hell))

theorem omega3_quotient_equation {N d p1 p2 p3 ell : ℕ}
    (hell : ell < N) (hdiv : d * p1 * p2 * p3 ∣ N - ell) :
    0 < omega3Quotient N d p1 p2 p3 ell ∧
      omega3Cofactor d p1 p2 (omega3Quotient N d p1 p2 p3 ell) * p3 = N - ell ∧
      ell = N - omega3Cofactor d p1 p2 (omega3Quotient N d p1 p2 p3 ell) * p3 ∧
      omega3Cofactor d p1 p2 (omega3Quotient N d p1 p2 p3 ell) * p3 ≤ N := by
  have hmul := Nat.mul_div_cancel' hdiv
  have heq : omega3Cofactor d p1 p2 (omega3Quotient N d p1 p2 p3 ell) * p3 =
      N - ell := by
    dsimp [omega3Cofactor, omega3Quotient]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hpos : 0 < omega3Quotient N d p1 p2 p3 ell := by
    by_contra h
    have hz : omega3Quotient N d p1 p2 p3 ell = 0 := by omega
    simp only [hz, omega3Cofactor, mul_zero, zero_mul] at heq
    omega
  refine ⟨hpos, heq, ?_, heq ▸ Nat.sub_le N ell⟩
  rw [heq, Nat.sub_sub_self hell.le]

theorem omega3_complement_div {N d p1 p2 p3 ell : ℕ}
    (hd : 0 < d) (hdiv : d * p1 * p2 * p3 ∣ N - ell) :
    (N - ell) / d = p1 * p2 * p3 * omega3Quotient N d p1 p2 p3 ell := by
  have h := Nat.mul_div_cancel' hdiv
  change d * p1 * p2 * p3 * omega3Quotient N d p1 p2 p3 ell = N - ell at h
  rw [← h]
  simpa only [mul_assoc] using
    Nat.mul_div_cancel_left (p1 * p2 * p3 * omega3Quotient N d p1 p2 p3 ell) hd

theorem omega3_quotient_coprime_of_output {N d p1 p2 p3 ell : ℕ}
    (hell : ell.Prime) (hellN : ell ≤ N) (hnot : ¬ell ∣ N)
    (hdiv : d * p1 * p2 * p3 ∣ N - ell) :
    (omega3Quotient N d p1 p2 p3 ell).Coprime N := by
  apply Nat.coprime_of_dvd
  intro q hq hqn hqN
  have hn : omega3Quotient N d p1 p2 p3 ell ∣ N - ell := by
    refine ⟨d * p1 * p2 * p3, ?_⟩
    exact (Nat.mul_div_cancel' hdiv).symm.trans (mul_comm _ _)
  have hqell : q ∣ ell := by
    have := Nat.dvd_sub hqN (hqn.trans hn)
    simpa only [Nat.sub_sub_self hellN] using this
  have he : q = ell := (Nat.dvd_prime hell).mp hqell |>.resolve_left hq.ne_one
  exact hnot (he ▸ hqN)

/-- Every additional exclusion follows from the literal source sieve
after removing just the shared-d and N-dividing-output labels. -/
theorem omega3_strengthened_of_source {N d p1 p2 p3 ell : ℕ}
    (hd : 0 < d) (h1 : p1.Prime) (h1N : p1.Coprime N) (h2N : p2.Coprime N)
    (hell : ell.Prime) (hellN : ell ≤ N)
    (hdiv : d * p1 * p2 * p3 ∣ N - ell)
    (hsieve : Sifted (d * p1 * N) (N - ell) (p2 : ℝ))
    (hgoodd : ¬Omega3BadD N d ell) (hgoodN : ¬ell ∣ N) :
    Omega3Strengthened N d p1 p2 (omega3Quotient N d p1 p2 p3 ell) := by
  let n := omega3Quotient N d p1 p2 p3 ell
  have hdcomp : d.Coprime (p1 * p2 * p3 * n) := by
    have h : d.Coprime ((N - ell) / d) := by simpa [Omega3BadD] using hgoodd
    simpa only [omega3_complement_div hd hdiv] using h
  have hpaird : (p1 * p2).Coprime d :=
    (hdcomp.of_dvd_right (by exact ⟨p3 * n, by ring⟩)).symm
  have hnd : n.Coprime d :=
    (hdcomp.of_dvd_right (dvd_mul_left n (p1 * p2 * p3))).symm
  have hnN : n.Coprime N := omega3_quotient_coprime_of_output hell hellN hgoodN hdiv
  refine ⟨hpaird.mul_right (h1N.mul_left h2N), hnd.mul_right hnN, ?_⟩
  intro q hq hsmall hne hqn
  have hqd : q.Coprime d := hnd.of_dvd_left hqn
  have hqN : q.Coprime N := hnN.of_dvd_left hqn
  have hq1 : q.Coprime p1 := (Nat.coprime_primes hq h1).mpr hne
  apply hsieve q hq ((hqd.mul_right hq1).mul_right hqN) hsmall
  have hn : n ∣ N - ell := by
    refine ⟨d * p1 * p2 * p3, ?_⟩
    exact (Nat.mul_div_cancel' hdiv).symm.trans (mul_comm _ _)
  exact hqn.trans hn

end Wu2008DoubleSieve
