import MIL.Independencep.definition

universe u
open Classical

section soundness


@[simp]
theorem id_A (m : model) (A: form)  : valuation m (A ≡ A) = tV.one := by
match test' (valuation m A) with
| TRI.one h =>
  simp [h]
| TRI.two h =>
  simp [h]
| TRI.three h =>
  simp [h]

theorem eq_subst (m : model) (A B : form) (s : oform) (h₁ :valuation m (A ≡ B) = tV.one):  valuation m (subst s A) = valuation m (subst s B) := by
  match s with
  | .atom n =>
    simp only [valuation]
  | .impl s t =>
    have hs : valuation m (subst s A) = valuation m (subst s B) := eq_subst m A B s h₁
    have ht : valuation m (subst t A) = valuation m (subst t B) := eq_subst m A B t h₁
    simp only [valuation, tV.impl]
    cases (tri_eq_case hs) <;> cases (tri_eq_case ht) <;> simp [*] at *
    -- match test' (valuation m (subst s A)), test' (valuation m (subst s B)) with
  | .neg s =>
    simp only [valuation]
    cases (tri_eq_case (eq_subst m A B s h₁)) <;> simp [*] at *
  | .id s t =>
    simp only [valuation]
    cases (tri_eq_case (eq_subst m A B s h₁)) <;> cases (tri_eq_case (eq_subst m A B t h₁)) <;> simp [*] at *
  | .free =>
    simp only [subst, valuation]
    exact eq_val_id h₁





theorem ax1.sound {m : model} {A B : form} (h₀ : (valuation m A) = tV.one ) : valuation m (A ⇒i (B ⇒i A)) = tV.one := by
    cases tri_eq_case h₀ <;>
    simp [*] at *

--这等价于以下的方式
theorem ax1.sound' (m : model) (A B : form) : valuation m (A ⇒i (B ⇒i A)) = tV.one := by
  match test' (valuation m A) with
  | TRI.one h =>
    match test' (valuation m B) with
    | TRI.one g => simp [h, g]
    | TRI.two g => simp [h, g]
    | TRI.three g => simp [h, g]
  | TRI.two h =>
    match test' (valuation m B) with
    | TRI.one g => simp [h, g]
    | TRI.two g => simp [h, g]
    | TRI.three g => simp [h, g]
  | TRI.three h =>
    match test' (valuation m B) with
    | TRI.one g => simp [h, g]
    | TRI.two g => simp [h, g]
    | TRI.three g => simp [h, g]


theorem ax2.sound (m : model) (A B C : form): valuation m ((A ⇒i (B ⇒i C)) ⇒i((A ⇒i B) ⇒i (A ⇒i C))) = tV.one := by
cases test' (valuation m A) <;>
cases test' (valuation m B) <;>
cases test' (valuation m C) <;>
simp [*] at *

theorem ax3.sound (m : model) (A : form) : valuation m (~~A ⇒i A) = tV.one := by
cases test' (valuation m A) <;>
simp [*] at *

theorem ax4.sound (m : model) (A : form) : valuation m (A ⇒i ~~A) = tV.one := by
cases test' (valuation m A) <;>
simp [*] at *

theorem ax5.sound (m : model) (A B : form) : valuation m ((~ A ⇒i ~ B) ⇒i (B ⇒i A)) = tV.one := by
cases test' (valuation m A) <;>
cases test' (valuation m B) <;>
simp [*] at *

theorem ax6.sound (m : model) (A : form) : valuation m (A ≡ A) = tV.one := by
cases test' (valuation m A) <;>
simp [*] at *


theorem ax7.sound {m : model} {A B : form} (f : oform) (h₀ : (valuation m (A ≡ B)) = tV.one) : valuation m ((subst f A) ⇒i (subst f B)) = tV.one := by
  match f with
  | .atom n =>
    cases test' (model.interpretation m n) <;>
    simp [*] at *
  | .impl s t =>
    have hs : (valuation m ((subst s A) ⇒i subst s B)) = tV.one := by exact ax7.sound s h₀
    have ht : (valuation m ((subst t A) ⇒i subst t B)) = tV.one := by exact ax7.sound t h₀
    dsimp
    have hes : valuation m (subst s A) =  valuation m (subst s B) := by exact eq_subst m A B s h₀
    have het : valuation m (subst t A) =  valuation m (subst t B) := by  exact eq_subst m A B t h₀
    cases tri_eq_case hes <;>
    cases tri_eq_case het <;>
    simp [*] at *
  | .neg s =>
    dsimp
    have hs : (valuation m (subst s A) = valuation m (subst s B)):= by exact eq_subst m A B s h₀
    cases tri_eq_case hs <;>
    simp [*] at *
  | .id s t =>
    have hs : (valuation m (subst s A) = valuation m (subst s B)):= by exact eq_subst m A B s h₀
    have ht : (valuation m (subst t A) = valuation m (subst t B)):= by exact eq_subst m A B t h₀
    cases tri_eq_case hs <;> cases tri_eq_case ht <;> simp [*] at *
  | .free =>
    dsimp
    cases tri_eq_case (eq_val_id h₀) <;> simp [*] at *

lemma mp_rule (m : model) (A B : form) : valuation m (A ⇒i ((A ⇒i B)⇒i A)) = tV.one := by
  cases test' (valuation m A) <;>
  cases test' (valuation m B) <;>
  simp [*] at *

end soundness
