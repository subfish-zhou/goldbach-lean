import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Wu18938Campaign.M2

theorem raw_product_selector (low : ℕ → Prop) {N d : ℕ} (l : List ℕ)
    (hprime : ∀ p ∈ l, p.Prime)
    (hcoprime : ∀ p ∈ l, p.Coprime N) :
    (∀ q : ℕ, q.Prime → q.Coprime (d * N) → low q → ¬q ∣ d * l.prod) ↔
      ∀ p ∈ l, low p → p ∣ d := by
  constructor
  · intro hs p hpl hl
    by_contra hd
    exact hs p (hprime p hpl)
      (((hprime p hpl).coprime_iff_not_dvd.mpr hd).mul_right (hcoprime p hpl))
      hl ((List.dvd_prod hpl).trans (dvd_mul_left l.prod d))
  · intro hsel q hq hc hl hd
    have hqd : ¬q ∣ d :=
      hq.coprime_iff_not_dvd.mp (hc.of_dvd_right (dvd_mul_right d N))
    have aux : ∀ a : List ℕ, (∀ p ∈ a, p.Prime) →
        (∀ p ∈ a, low p → p ∣ d) → ¬q ∣ a.prod := by
      intro a
      induction a with
      | nil =>
        intro _ _
        exact hq.not_dvd_one
      | cons p a ih =>
        intro hp hs hdiv
        rcases hq.dvd_mul.mp hdiv with hqp | hqa
        · have heq : q = p :=
            ((Nat.dvd_prime (hp p (by simp))).mp hqp).resolve_left hq.ne_one
          subst p
          exact hqd (hs q (by simp) hl)
        · exact ih (fun p hp' => hp p (by simp [hp']))
            (fun p hp' => hs p (by simp [hp'])) hqa
    exact (hq.dvd_mul.mp hd).elim hqd (aux l hprime hsel)

theorem raw_prime_forces_square (low : ℕ → Prop) {N d L n p : ℕ}
    (hp : p.Prime) (hpN : p.Coprime N) (hpL : p ∣ L)
    (hDn : d * L ∣ n) (hlow : low p)
    (hraw : ∀ q : ℕ, q.Prime → q.Coprime (d * N) → low q → ¬q ∣ n) :
    p ∣ d ∧ p ^ 2 ∣ n := by
  have hpd : p ∣ d := by
    by_contra hn
    exact hraw p hp ((hp.coprime_iff_not_dvd.mpr hn).mul_right hpN) hlow
      ((hpL.trans (dvd_mul_left L d)).trans hDn)
  refine ⟨hpd, ?_⟩
  have hpp : p * p ∣ d * L := Nat.mul_dvd_mul hpd hpL
  simpa only [pow_two] using hpp.trans hDn

theorem raw_squarefree_excludes_label (low : ℕ → Prop) {N d L n p : ℕ}
    (hp : p.Prime) (hpN : p.Coprime N) (hpL : p ∣ L)
    (hDn : d * L ∣ n) (hsf : Squarefree n)
    (hraw : ∀ q : ℕ, q.Prime → q.Coprime (d * N) → low q → ¬q ∣ n) :
    ¬low p := by
  intro hl
  have hs := (raw_prime_forces_square low hp hpN hpL hDn hl hraw).2
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp (by simpa only [pow_two] using hs)

end Wu18938Campaign.M2
