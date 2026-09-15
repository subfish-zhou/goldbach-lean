import MathlibNt.Wu2008DoubleSieve.TruncatedElevenSignedLower
import MathlibNt.Wu2008DoubleSieve.FourModulusTransportPayment

/-! Label-preserving physical cofactors for the original tenth and eleventh terms.
The physical residual is an arbitrary natural integer greater than one. -/
namespace Wu2008DoubleSieve.TruncatedFourPhysical
open Finset Real
open scoped Classical

abbrev Quad := ℕ × ℕ × ℕ × ℕ
abbrev Label := Σ _ : Quad, ℕ

noncomputable def raw (N : ℕ) (S : Finset Quad) : Finset Label :=
  S.sigma fun t => sieveCarrier N (fourModulusProduct t) N t.2.1

noncomputable def physical (N : ℕ) (S : Finset Quad) : Finset Label :=
  S.sigma fun t => (range (N+1)).filter fun n =>
    1 < n ∧ LiLiuPrereqBuchstab.Rough (t.2.1 : ℝ) n ∧
      fourModulusProduct t*n < N ∧ (N-fourModulusProduct t*n).Prime

noncomputable def exceptional (N : ℕ) (S : Finset Quad) : Finset Label :=
  (raw N S).filter fun x => x.2 ∣ N ∨ N-x.2 = fourModulusProduct x.1

noncomputable def good (N : ℕ) (S : Finset Quad) : Finset Label :=
  (raw N S).filter fun x => ¬(x.2 ∣ N ∨ N-x.2 = fourModulusProduct x.1)

def switch (N : ℕ) (x : Label) : Label :=
  ⟨x.1, (N-x.2)/fourModulusProduct x.1⟩

theorem raw_mem {N : ℕ} {S : Finset Quad} {x : Label} (hx : x ∈ raw N S) :
    x.1 ∈ S ∧ x.2 ≤ N ∧ x.2.Prime ∧ fourModulusProduct x.1 ∣ N-x.2 ∧
      Sifted N ((N-x.2)/fourModulusProduct x.1) x.1.2.1 := by
  simpa only [raw, mem_sigma, sieveCarrier, mem_filter, mem_range,
    Nat.lt_succ_iff, and_assoc] using hx

theorem prime_lt_even {N p : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hp : p.Prime) (hpN : p ≤ N) : p < N := by
  rcases hp.eq_two_or_odd with h | h
  · omega
  · have hn := he.two_dvd
    have hm := Nat.mod_eq_zero_of_dvd hn
    omega

theorem quotient_rough {N D p : ℕ} {b : ℝ} (hpN : p ≤ N)
    (hd : D ∣ N-p) (hs : Sifted N ((N-p)/D) b) (hp : p.Prime)
    (hgood : ¬p ∣ N) : LiLiuPrereqBuchstab.Rough b ((N-p)/D) := by
  intro q hq hqn
  by_contra h
  have hqD : q ∣ N-p := by
    rw [← Nat.mul_div_cancel' hd]
    exact dvd_mul_of_dvd_right hqn D
  have hqcop : q.Coprime N := by
    apply hq.coprime_iff_not_dvd.mpr
    intro hqN
    have hqp : q ∣ p := by
      have := Nat.dvd_sub hqN hqD
      simpa only [Nat.sub_sub_self hpN] using this
    have heq := (Nat.dvd_prime hp).mp hqp
    rcases heq with heq | heq
    · exact hq.ne_one heq
    · subst q
      exact hgood hqN
  exact hs q hq hqcop (lt_of_not_ge h) hqn

theorem domain_product_pos {N : ℕ} {z w V : ℝ} {t : Quad}
    (ht : t ∈ fourModulusDomain N z w V) : 0 < fourModulusProduct t := by
  rcases t with ⟨a,b,c,d⟩
  obtain ⟨ha,_,_,hb,_,hc,_,hd,_⟩ := fourModulusDomain_labels ht
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) hd.pos

theorem good_maps {N : ℕ} {S : Finset Quad}
    (hN : 4 ≤ N) (he : Even N) :
    Set.MapsTo (switch N) (good N S) (physical N S) := by
  intro x hx
  obtain ⟨hx,hxgood⟩ := mem_filter.mp hx
  obtain ⟨ht,hpN,hp,hd,hs⟩ := raw_mem hx
  have hlt := prime_lt_even hN he hp hpN
  have hmul := Nat.mul_div_cancel' hd
  have hnpos : 0 < (N-x.2)/fourModulusProduct x.1 := by
    by_contra h
    have hz : (N-x.2)/fourModulusProduct x.1 = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hmul
    omega
  have hn1 : (N-x.2)/fourModulusProduct x.1 ≠ 1 := by
    intro hn
    rw [hn, mul_one] at hmul
    exact hxgood (Or.inr hmul.symm)
  change switch N x ∈ physical N S
  dsimp only [switch]
  apply mem_sigma.mpr
  refine ⟨ht, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩⟩
  · exact Nat.lt_succ_of_le ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))
  · change 1 < (N-x.2)/fourModulusProduct x.1 ∧ _
    refine ⟨by omega, quotient_rough hpN hd hs hp (fun h => hxgood (Or.inl h)), ?_, ?_⟩
    · rw [hmul]
      exact Nat.sub_lt (by omega) hp.pos
    · rw [hmul, Nat.sub_sub_self hpN]
      exact hp

theorem switch_inj {N : ℕ} {S : Finset Quad} :
    Set.InjOn (switch N) (raw N S) := by
  rintro ⟨t,p⟩ hx ⟨u,q⟩ hy h
  have ht : t = u := congrArg Sigma.fst h
  subst u
  have hn : (N-p)/fourModulusProduct t = (N-q)/fourModulusProduct t := by
    simpa only [switch, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  obtain ⟨_,hp,_,hd,_⟩ := raw_mem hx
  obtain ⟨_,hq,_,he,_⟩ := raw_mem hy
  dsimp only at hp hq hd he
  have hh := congrArg (fun n => fourModulusProduct t*n) hn
  rw [Nat.mul_div_cancel' hd, Nat.mul_div_cancel' he] at hh
  have : p = q := by omega
  subst q
  rfl

theorem raw_le_physical_exceptional {N : ℕ} {S : Finset Quad}
    (hN : 4 ≤ N) (he : Even N) :
    (raw N S).card ≤ (physical N S).card + (exceptional N S).card := by
  have hg : (good N S).card ≤ (physical N S).card :=
    card_le_card_of_injOn (switch N) (good_maps hN he)
      (switch_inj.mono (filter_subset _ _))
  have hh := card_filter_add_card_filter_not (s := raw N S)
    (p := fun x => x.2 ∣ N ∨ N-x.2 = fourModulusProduct x.1)
  change (exceptional N S).card + (good N S).card = (raw N S).card at hh
  omega

/-- Integer source sum followed by its exact real cast. -/
theorem source_cast (N : ℕ) (S : Finset Quad) :
    ((∑ t ∈ S, sieveCount N (fourModulusProduct t) N (t.2.1 : ℝ) : ℤ) : ℝ) =
      ((raw N S).card : ℝ) := by
  simp only [raw, card_sigma, sieveCount, Int.cast_sum, Int.cast_natCast, Nat.cast_sum]

end Wu2008DoubleSieve.TruncatedFourPhysical
