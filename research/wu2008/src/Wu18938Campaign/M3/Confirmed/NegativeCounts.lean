import WSrcFourEnclosureResult
import Wu18938Campaign.M3.Confirmed.FiniteMother

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Wu2008DoubleSieve Wu08TerminalAlignment
open SeventhEighth U8MotherInsertion

theorem original_seventh_eighth_actual_upper {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2*(lowerS2 N ((N:ℝ)^truncatedSixthLowerBeta)
        ((N:ℝ)^truncatedSixthLowerSigma) : ℝ) +
        (lowerS3 N ((N:ℝ)^truncatedSixthLowerAlpha) ((N:ℝ)^(1/3:ℝ)) : ℝ) ≤
      (2*seventhMain+eighthMain+ε)*truncatedSixthMassScale N := by
  have he5 : 0 < ε/5 := by positivity
  obtain ⟨Tw,hTw,hw⟩ := fixed_weighted_switching_epsilon he5
  obtain ⟨T7,_,h7⟩ := seventh_eighth_physical_classical_upper he5
  obtain ⟨Tl,_,hl⟩ := large_integral_upper he5
  obtain ⟨Ts,hs⟩ := OriginalU8.Weighted.physicalSmall_original_integral (ε/5) he5
  refine ⟨max Tw (max T7 (max Tl Ts)),by omega,fun N hN hEven => ?_⟩
  have hwN := hw N (by omega) hEven
  have h7N := (h7 N (by omega) hEven).1
  have hlN := hl N (by omega) hEven
  have hsN := hs N (by omega) hEven
  have hsM : ((small N).card : ℝ) ≤
      (8*U8CanonicalMother.I+ε/5)*truncatedSixthMassScale N := by
    rw [U8CanonicalMother.small_eq_physicalSmall,
      truncatedSixthMassScale, wuSingularSeries_eq_liu N (by omega)]
    convert hsN using 1
    ring
  change ((2*lowerS2 N ((N:ℝ)^truncatedSixthLowerBeta)
    ((N:ℝ)^truncatedSixthLowerSigma) +
      lowerS3 N ((N:ℝ)^truncatedSixthLowerAlpha) ((N:ℝ)^(1/3:ℝ)) : ℤ) : ℝ) ≤ _ at hwN
  rw [physicalT8_card_split, Nat.cast_add] at hwN
  push_cast at hwN
  unfold seventhMain eighthMain
  rw [J8_split]
  change _ ≤ (2*(8*J7)+(8*(oldSmallIntegral+largeIntegral)-
    8*(oldSmallIntegral-U8CanonicalMother.I))+ε)*truncatedSixthMassScale N
  unfold truncatedSixthMassScale at hsM ⊢
  ring_nf at hwN h7N hlN hsM ⊢
  linarith only [hwN,h7N,hlN,hsM]

theorem original_four_actual_upper {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        ((851/1250:ℝ)+ε)*truncatedSixthMassScale N :=
  WuSource.SrcFourEnclosure.actual_pair_upper he

end Wu18938Campaign.M3.Confirmed
