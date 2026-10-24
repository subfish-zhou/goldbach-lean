import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints027
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_027 (j : Fin 16) : terminalPayment (16*27+j.val) ≤
    terminalValue ((point cut hi 1024 (16*27+j.val)+point cut hi 1024 (16*27+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 432 ≤ terminalValue ((point cut hi 1024 432+point cut hi 1024 433)/2)
    have hp : terminalPayment 432 = (473049703609:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 432+point cut hi 1024 433)/2 = (180668863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180668863:ℝ)/42188800) = (2282601:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180668863:ℝ)/42188800)-4 = (11913663:ℝ)/42188800 by norm_num]
    exact paid_terminal_432
  · change terminalPayment 433 ≤ terminalValue ((point cut hi 1024 433+point cut hi 1024 434)/2)
    have hp : terminalPayment 433 = (472486604242:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 433+point cut hi 1024 434)/2 = (180694013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180694013:ℝ)/42188800) = (2281595:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180694013:ℝ)/42188800)-4 = (11938813:ℝ)/42188800 by norm_num]
    exact paid_terminal_433
  · change terminalPayment 434 ≤ terminalValue ((point cut hi 1024 434+point cut hi 1024 435)/2)
    have hp : terminalPayment 434 = (471922881771:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 434+point cut hi 1024 435)/2 = (180719163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180719163:ℝ)/42188800) = (2280589:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180719163:ℝ)/42188800)-4 = (11963963:ℝ)/42188800 by norm_num]
    exact paid_terminal_434
  · change terminalPayment 435 ≤ terminalValue ((point cut hi 1024 435+point cut hi 1024 436)/2)
    have hp : terminalPayment 435 = (471358535502:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 435+point cut hi 1024 436)/2 = (180744313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180744313:ℝ)/42188800) = (2279583:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180744313:ℝ)/42188800)-4 = (11989113:ℝ)/42188800 by norm_num]
    exact paid_terminal_435
  · change terminalPayment 436 ≤ terminalValue ((point cut hi 1024 436+point cut hi 1024 437)/2)
    have hp : terminalPayment 436 = (470793564737:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 436+point cut hi 1024 437)/2 = (180769463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180769463:ℝ)/42188800) = (2278577:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180769463:ℝ)/42188800)-4 = (12014263:ℝ)/42188800 by norm_num]
    exact paid_terminal_436
  · change terminalPayment 437 ≤ terminalValue ((point cut hi 1024 437+point cut hi 1024 438)/2)
    have hp : terminalPayment 437 = (470227968779:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 437+point cut hi 1024 438)/2 = (180794613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180794613:ℝ)/42188800) = (2277571:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180794613:ℝ)/42188800)-4 = (12039413:ℝ)/42188800 by norm_num]
    exact paid_terminal_437
  · change terminalPayment 438 ≤ terminalValue ((point cut hi 1024 438+point cut hi 1024 439)/2)
    have hp : terminalPayment 438 = (469661746928:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 438+point cut hi 1024 439)/2 = (180819763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180819763:ℝ)/42188800) = (2276565:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180819763:ℝ)/42188800)-4 = (12064563:ℝ)/42188800 by norm_num]
    exact paid_terminal_438
  · change terminalPayment 439 ≤ terminalValue ((point cut hi 1024 439+point cut hi 1024 440)/2)
    have hp : terminalPayment 439 = (469094898486:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 439+point cut hi 1024 440)/2 = (180844913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180844913:ℝ)/42188800) = (2275559:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180844913:ℝ)/42188800)-4 = (12089713:ℝ)/42188800 by norm_num]
    exact paid_terminal_439
  · change terminalPayment 440 ≤ terminalValue ((point cut hi 1024 440+point cut hi 1024 441)/2)
    have hp : terminalPayment 440 = (468527422750:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 440+point cut hi 1024 441)/2 = (180870063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180870063:ℝ)/42188800) = (2274553:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180870063:ℝ)/42188800)-4 = (12114863:ℝ)/42188800 by norm_num]
    exact paid_terminal_440
  · change terminalPayment 441 ≤ terminalValue ((point cut hi 1024 441+point cut hi 1024 442)/2)
    have hp : terminalPayment 441 = (467959319019:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 441+point cut hi 1024 442)/2 = (180895213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180895213:ℝ)/42188800) = (2273547:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180895213:ℝ)/42188800)-4 = (12140013:ℝ)/42188800 by norm_num]
    exact paid_terminal_441
  · change terminalPayment 442 ≤ terminalValue ((point cut hi 1024 442+point cut hi 1024 443)/2)
    have hp : terminalPayment 442 = (467390586588:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 442+point cut hi 1024 443)/2 = (180920363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180920363:ℝ)/42188800) = (2272541:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180920363:ℝ)/42188800)-4 = (12165163:ℝ)/42188800 by norm_num]
    exact paid_terminal_442
  · change terminalPayment 443 ≤ terminalValue ((point cut hi 1024 443+point cut hi 1024 444)/2)
    have hp : terminalPayment 443 = (466821224754:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 443+point cut hi 1024 444)/2 = (180945513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180945513:ℝ)/42188800) = (2271535:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180945513:ℝ)/42188800)-4 = (12190313:ℝ)/42188800 by norm_num]
    exact paid_terminal_443
  · change terminalPayment 444 ≤ terminalValue ((point cut hi 1024 444+point cut hi 1024 445)/2)
    have hp : terminalPayment 444 = (466251232810:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 444+point cut hi 1024 445)/2 = (180970663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180970663:ℝ)/42188800) = (2270529:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180970663:ℝ)/42188800)-4 = (12215463:ℝ)/42188800 by norm_num]
    exact paid_terminal_444
  · change terminalPayment 445 ≤ terminalValue ((point cut hi 1024 445+point cut hi 1024 446)/2)
    have hp : terminalPayment 445 = (465680610049:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 445+point cut hi 1024 446)/2 = (180995813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180995813:ℝ)/42188800) = (2269523:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180995813:ℝ)/42188800)-4 = (12240613:ℝ)/42188800 by norm_num]
    exact paid_terminal_445
  · change terminalPayment 446 ≤ terminalValue ((point cut hi 1024 446+point cut hi 1024 447)/2)
    have hp : terminalPayment 446 = (465109355764:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 446+point cut hi 1024 447)/2 = (181020963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181020963:ℝ)/42188800) = (2268517:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181020963:ℝ)/42188800)-4 = (12265763:ℝ)/42188800 by norm_num]
    exact paid_terminal_446
  · change terminalPayment 447 ≤ terminalValue ((point cut hi 1024 447+point cut hi 1024 448)/2)
    have hp : terminalPayment 447 = (464537469245:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 447+point cut hi 1024 448)/2 = (181046113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181046113:ℝ)/42188800) = (2267511:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181046113:ℝ)/42188800)-4 = (12290913:ℝ)/42188800 by norm_num]
    exact paid_terminal_447
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_027
