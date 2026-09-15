import MathlibNt.Wu2008DoubleSieve.LastPrimeFourSieveCore
import MathlibNt.Wu2008DoubleSieve.FourRoughClosedMass

/-! A five-label injection for the entire prime profile, before testing the
output. Strict windows enlarge to closed windows and the last-prime coprimality
screen remains absent on both sides. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real LiLiuPrereqBuchstab
open scoped Classical

noncomputable def fourFullProfiles (N : ℕ) (e : Bool) : Finset (Σ _ : Index, ℕ) :=
  (labels N e).sigma fun t => omega3ProfilePrimes N (lower N e t) (upper N e t)
noncomputable def fourClosedLabels (N : ℕ) (e : Bool) : Finset TruncatedFourPhysical.Quad :=
  if e then FourRoughClosedMass.labels11 N else FourRoughClosedMass.labels10 N
noncomputable def fourRawMass (N : ℕ) (e : Bool) : ℝ :=
  if e then FourRoughClosedMass.rawMass11 N else FourRoughClosedMass.rawMass10 N

def unswitch (x : Σ _ : Index, ℕ) : TruncatedFourPhysical.Label :=
  ⟨(x.1.1,x.1.2.1,x.1.2.2.1,x.2),x.1.2.2.2⟩

theorem unswitch_injective : Function.Injective unswitch := by
  intro x y h
  have hs := congrArg switch h
  simpa only [switch, unswitch] using hs

theorem fourFullProfiles_mass (N : ℕ) (e : Bool) :
    ((fourFullProfiles N e).card : ℝ) = fourMass N e := by
  simp only [fourFullProfiles, card_sigma, Nat.cast_sum, fourMass]

theorem fourFullProfiles_maps {N : ℕ} {e : Bool} :
    Set.MapsTo unswitch (fourFullProfiles N e)
      ((fourClosedLabels N e).sigma fun q => FourRoughClosedMass.cofactor N q) := by
  rintro ⟨⟨a,b,c,n⟩,d⟩ hx
  obtain ⟨ht,hd⟩ := mem_sigma.mp hx
  obtain ⟨ha,_,hza,hb,_,hc,_,hab,hbc,hcw,hn,hr⟩ := base_data (labels_base ht)
  obtain ⟨_,hdP,hlo,hup⟩ := mem_filter.mp hd
  obtain ⟨hcd,hwd⟩ := (lower_iff N d e (a,b,c,n)).mp hlo
  have hN : 0 < N := lt_of_lt_of_le (label_geometry ht).1 (label_le_N ht)
  obtain ⟨hcap,hs⟩ := (upper_iff hN e _ (label_geometry ht).1 d).mp hup
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hbcR : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
  have hcdR : (c : ℝ) ≤ d := by exact_mod_cast hcd.le
  have hw : 0 ≤ (N : ℝ)^FourRoughClosedMass.beta := rpow_nonneg (Nat.cast_nonneg _) _
  have hlabels : (a,b,c,d) ∈ fourClosedLabels N e := by
    cases e
    · apply FourRoughClosedMass.mem_labels.mpr
      exact ⟨(mem_primesIcc hw).mpr ⟨ha,hza,habR.trans (hbcR.trans hcw.le)⟩,
        (mem_primesIcc hw).mpr ⟨hb,habR,hbcR.trans hcw.le⟩,
        (mem_primesIcc hw).mpr ⟨hc,hbcR,hcw.le⟩,
        (mem_primesIcc hw).mpr ⟨hdP,hcdR,hcap.le⟩⟩
    · apply FourRoughClosedMass.mem_labels.mpr
      have hv : 0 ≤ (N : ℝ)^FourRoughClosedMass.lam / c := by positivity
      exact ⟨(mem_primesIcc hw).mpr ⟨ha,hza,habR.trans (hbcR.trans hcw.le)⟩,
        (mem_primesIcc hw).mpr ⟨hb,habR,hbcR.trans hcw.le⟩,
        (mem_primesIcc hw).mpr ⟨hc,hbcR,hcw.le⟩,
        (mem_primesIcc hv).mpr ⟨hdP,hwd rfl,hcap.le⟩⟩
  have hD : 0 < fourModulusProduct (a,b,c,d) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) hdP.pos
  have hid : fourModulusProduct (a,b,c,d)*n = cofactor (a,b,c,n)*d := by
    simp only [fourModulusProduct, cofactor]; ring
  have hprod : fourModulusProduct (a,b,c,d)*n < N := hid.symm ▸ hs
  have hnN : n ≤ N := (Nat.le_mul_of_pos_left n hD).trans hprod.le
  have hf : n ∈ FourRoughClosedMass.strictFibre N (a,b,c,d) :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),hn,hr,hprod⟩
  exact mem_sigma.mpr ⟨hlabels,FourRoughClosedMass.strictFibre_subset hD hf⟩

/-- The full mass counts all d-primes, not just prime outputs. The map preserves
all five coordinates and drops no multiplicity. Enlargement is an inequality. -/
theorem fourMass_le_rawMass (N : ℕ) (e : Bool) : fourMass N e ≤ fourRawMass N e := by
  have hc := card_le_card_of_injOn unswitch (fourFullProfiles_maps (N := N) (e := e))
    unswitch_injective.injOn
  rw [← fourFullProfiles_mass]
  have hm : (((fourClosedLabels N e).sigma fun q =>
      FourRoughClosedMass.cofactor N q).card : ℝ) = fourRawMass N e := by
    cases e <;> simp only [fourClosedLabels, fourRawMass, Bool.false_eq_true, if_false,
      if_true, FourRoughClosedMass.rawMass10, FourRoughClosedMass.rawMass11,
      FourRoughClosedMass.mass, card_sigma, Nat.cast_sum]
  exact (show (_ : ℝ) ≤ _ by exact_mod_cast hc).trans_eq hm

end Wu2008DoubleSieve.LastPrimeFour
