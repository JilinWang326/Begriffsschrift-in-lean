import MIL.Independencep.definition
import MIL.Independencep.valid


theorem IV_Indep (m : model) (A B : form)(h₀ : valuation m A = tV.two) (h₁ : valuation m B = tV.three) : valuation m (~(A ≡ (~B) ) ⇒i (A ≡ B)) = tV.two := by
  cases test' (valuation m A) <;>
  cases test' (valuation m B) <;>
  simp [*] at *

theorem BB_Indep (m : model) (A B : form)(h₀ : valuation m A = tV.two) (h₁ : valuation m B = tV.three) : valuation m ((A ⇒i B ) ⇒i (B ⇒i A) ⇒i (A ≡ B)) = tV.two := by
  cases test' (valuation m A) <;>
  cases test' (valuation m B) <;>
  simp [*] at *

theorem NN_Indep (m : model) (A : form) (h₀ : valuation m A = tV.three) : valuation m ((~(~A)) ≡  A) = tV.three := by
  cases test' (valuation m A) <;>
  simp [*] at *
