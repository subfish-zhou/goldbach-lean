import WR2ClassicalFifthIntegerData

namespace WuPaper.ClassicalFifthRational
open Finset

def initialNumerator (i : ℕ) : ℕ := FifthIntegerPayment.paymentNumerator .initial i
def initialPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ range 64, initialNumerator (64*b+j)

def middleNumerator (i : ℕ) : ℕ := FifthIntegerPayment.paymentNumerator .middle i
def middlePaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ range 64, middleNumerator (64*b+j)

def terminalNumerator (i : ℕ) : ℕ := FifthIntegerPayment.paymentNumerator .terminal i
def terminalPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ range 64, terminalNumerator (64*b+j)

end WuPaper.ClassicalFifthRational
