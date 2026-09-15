import MathlibNt.Wu2008DoubleSieve.LastPrimeFourProfiles

/-! A literal injection retains all four original prime labels and the rough
integer. Only the last prime's coprimality mask is dropped in the upper bound. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real
open scoped Classical

noncomputable def original (N : ℕ) (e : Bool) : Finset TruncatedFourPhysical.Label :=
  if e then TruncatedFourPhysical.Physical11 N else TruncatedFourPhysical.Physical10 N

def switch (x : TruncatedFourPhysical.Label) : Σ _ : Index, ℕ :=
  ⟨(x.1.1, x.1.2.1, x.1.2.2.1, x.2), x.1.2.2.2⟩

noncomputable def outputProfiles (N : ℕ) (e : Bool) : Finset (Σ _ : Index, ℕ) :=
  (labels N e).sigma fun t =>
    (omega3ProfilePrimes N (lower N e t) (upper N e t)).filter
      fun d => (N-cofactor t*d).Prime

/-- The unrounded last-prime conditions on each original physical label. -/
theorem original_data {N a b c d n : ℕ} {e : Bool}
    (hx : (⟨(a,b,c,d),n⟩ : TruncatedFourPhysical.Label) ∈ original N e) :
    a.Prime ∧ a.Coprime N ∧ z N ≤ a ∧ b.Prime ∧ b.Coprime N ∧
      c.Prime ∧ c.Coprime N ∧ a < b ∧ b < c ∧ (c : ℝ) < w N ∧
      1 < n ∧ LiLiuPrereqBuchstab.Rough (b : ℝ) n ∧
      d.Prime ∧ d.Coprime N ∧ c < d ∧ (e = true → w N ≤ d) ∧
      (d : ℝ) < cap N e (a,b,c,n) ∧
      cofactor (a,b,c,n)*d < N ∧ (N-cofactor (a,b,c,n)*d).Prime := by
  have hid : fourModulusProduct (a,b,c,d)*n = cofactor (a,b,c,n)*d := by
    simp only [fourModulusProduct, cofactor]; ring
  cases e
  · obtain ⟨ht,hn,hr,hlt,hp⟩ :=
      (TruncatedFourPhysical.Physical10_mem N (a,b,c,d) n).mp hx
    obtain ⟨ha,haN,hza,hb,hbN,hc,hcN,hd,hdN,hdw,hab,hbc,hcd⟩ :=
      mem_s3_first_quadruples.mp ht
    have hcw : (c : ℝ) < w N := (show (c : ℝ) < d by exact_mod_cast hcd).trans hdw
    exact ⟨ha,haN,hza,hb,hbN,hc,hcN,hab,hbc,hcw,hn,hr,hd,hdN,hcd,
      by simp,hdw,hid ▸ hlt,hid ▸ hp⟩
  · obtain ⟨ht,hn,hr,hlt,hp⟩ :=
      (TruncatedFourPhysical.Physical11_mem N (a,b,c,d) n).mp hx
    obtain ⟨ha,haN,hza,hb,hbN,hc,hcN,hd,hdN,hab,hbc,hcw,hwd,hdv⟩ :=
      mem_s3Upsilon11Range.mp ht
    have hcd : c < d := by exact_mod_cast hcw.trans_le hwd
    exact ⟨ha,haN,hza,hb,hbN,hc,hcN,hab,hbc,hcw,hn,hr,hd,hdN,hcd,
      fun _ => hwd,hdv,hid ▸ hlt,hid ▸ hp⟩

theorem switch_injective : Function.Injective switch := by
  rintro ⟨⟨a,b,c,d⟩,n⟩ ⟨⟨a',b',c',d'⟩,n'⟩ h
  have ht := congrArg Sigma.fst h
  have hd : d = d' := by simpa only [switch, Sigma.mk.inj_iff, heq_eq_eq] using
    (show (switch ⟨(a,b,c,d),n⟩).2 = (switch ⟨(a',b',c',d'),n'⟩).2 from
      congrArg (fun x : Σ _ : Index, ℕ => x.2) h)
  have ha := congrArg Prod.fst ht
  have hb := congrArg (fun t : Index => t.2.1) ht
  have hc := congrArg (fun t : Index => t.2.2.1) ht
  have hn := congrArg (fun t : Index => t.2.2.2) ht
  dsimp only [switch] at ha hb hc hn
  subst a'; subst b'; subst c'; subst d'; subst n'
  rfl

theorem original_maps {N : ℕ} {e : Bool} :
    Set.MapsTo switch (original N e) (outputProfiles N e) := by
  rintro ⟨⟨a,b,c,d⟩,n⟩ hx
  obtain ⟨ha,haN,hza,hb,hbN,hc,hcN,hab,hbc,hcw,hn,hr,hd,_,hcd,hwd,hcap,hs,hout⟩ :=
    original_data hx
  have hm : 0 < cofactor (a,b,c,n) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) (show 0 < n by omega)
  have hdN : d ≤ N := (Nat.le_mul_of_pos_left d hm).trans hs.le
  have hnN : n ≤ N := by
    have hh : n ≤ cofactor (a,b,c,n) :=
      Nat.le_mul_of_pos_left n (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos)
    exact hh.trans ((Nat.le_mul_of_pos_right _ hd.pos).trans hs.le)
  have ht : (a,b,c,n) ∈ base N := by
    apply mem_filter.mpr
    refine ⟨?_,ha,haN,hza,hb,hbN,hc,hcN,hab,hbc,hcw,hn,hr⟩
    simp only [mem_product, mem_range]
    omega
  have hp : d ∈ omega3ProfilePrimes N (lower N e (a,b,c,n)) (upper N e (a,b,c,n)) := by
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by omega),hd,(lower_iff N d e _).mpr ⟨hcd,hwd⟩,
      (upper_iff (by omega) e _ hm d).mpr ⟨hcap,hs⟩⟩
  exact mem_sigma.mpr ⟨mem_filter.mpr ⟨ht,⟨d,hp⟩⟩,mem_filter.mpr ⟨hp,hout⟩⟩

/-- No output-image quotient: the injection retains `(a,b,c,n,d)` separately.
The right side enlarges only the `d.Coprime N` condition. -/
theorem original_card_le_profiles (N : ℕ) (e : Bool) :
    (original N e).card ≤ ∑ t ∈ labels N e,
      ((omega3ProfilePrimes N (lower N e t) (upper N e t)).filter
        (fun d => (N-cofactor t*d).Prime)).card := by
  calc
    _ ≤ (outputProfiles N e).card :=
      card_le_card_of_injOn switch original_maps switch_injective.injOn
    _ = _ := card_sigma _ _

theorem physical10_card_le (N : ℕ) :
    (TruncatedFourPhysical.Physical10 N).card ≤ ∑ t ∈ labels N false,
      ((omega3ProfilePrimes N (lower N false t) (upper N false t)).filter
        (fun d => (N-cofactor t*d).Prime)).card := original_card_le_profiles N false

theorem physical11_card_le (N : ℕ) :
    (TruncatedFourPhysical.Physical11 N).card ≤ ∑ t ∈ labels N true,
      ((omega3ProfilePrimes N (lower N true t) (upper N true t)).filter
        (fun d => (N-cofactor t*d).Prime)).card := original_card_le_profiles N true

/-- Restoring just the original last-prime coprimality mask gives the reverse
map. In particular the enlargement did not alter roughness or any strict face. -/
theorem profiles_restore_original {N : ℕ} {e : Bool} {a b c n d : ℕ}
    (hx : (⟨(a,b,c,n),d⟩ : Σ _ : Index, ℕ) ∈ outputProfiles N e)
    (hdN : d.Coprime N) :
    (⟨(a,b,c,d),n⟩ : TruncatedFourPhysical.Label) ∈ original N e := by
  obtain ⟨ht,hd⟩ := mem_sigma.mp hx
  obtain ⟨ha,haN,hza,hb,hbN,hc,hcN,hab,hbc,hcw,hn,hr⟩ :=
    base_data (labels_base ht)
  obtain ⟨hd,hout⟩ := mem_filter.mp hd
  obtain ⟨_,hdP,hlo,hup⟩ := mem_filter.mp hd
  obtain ⟨hcd,hwd⟩ := (lower_iff N d e (a,b,c,n)).mp hlo
  have hN : 0 < N := lt_of_lt_of_le (label_geometry ht).1 (label_le_N ht)
  obtain ⟨hcap,hs⟩ := (upper_iff hN e _ (label_geometry ht).1 d).mp hup
  have hid : fourModulusProduct (a,b,c,d)*n = cofactor (a,b,c,n)*d := by
    simp only [fourModulusProduct, cofactor]; ring
  cases e
  · apply (TruncatedFourPhysical.Physical10_mem N (a,b,c,d) n).mpr
    refine ⟨mem_s3_first_quadruples.mpr ?_,hn,hr,hid.symm ▸ hs,hid.symm ▸ hout⟩
    exact ⟨ha,haN,hza,hb,hbN,hc,hcN,hdP,hdN,hcap,hab,hbc,hcd⟩
  · apply (TruncatedFourPhysical.Physical11_mem N (a,b,c,d) n).mpr
    refine ⟨mem_s3Upsilon11Range.mpr ?_,hn,hr,hid.symm ▸ hs,hid.symm ▸ hout⟩
    exact ⟨ha,haN,hza,hb,hbN,hc,hcN,hdP,hdN,hab,hbc,hcw,hwd rfl,hcap⟩

/-- A literal label-by-label equivalence, before discarding the d mask. -/
theorem original_iff_profile {N : ℕ} {e : Bool} (a b c d n : ℕ) :
    (⟨(a,b,c,d),n⟩ : TruncatedFourPhysical.Label) ∈ original N e ↔
      (⟨(a,b,c,n),d⟩ : Σ _ : Index, ℕ) ∈ outputProfiles N e ∧ d.Coprime N := by
  constructor
  · intro hx
    exact ⟨original_maps hx,(original_data hx).2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  · rintro ⟨hx,hcop⟩
    exact profiles_restore_original hx hcop

end Wu2008DoubleSieve.LastPrimeFour
