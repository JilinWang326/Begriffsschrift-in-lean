import Mathlib.Tactic
inductive form : Type
| atom : Nat → form
| impl : form → form → form
| neg : form → form
| id : form → form → form

notation "# " n => form.atom n
notation p " ⇒i " q => form.impl p q
notation "~ " p => form.neg p
notation p " ≡ " q => form.id p q

@[simp]
def form.substitution2 (r : form) (x : Nat) (A : form) : form :=
  match r with
  | # m => if x = m then A else r
  | p ⇒i q => (p.substitution2 x A) ⇒i (q.substitution2 x A)
  | ~ p => ~ (p.substitution2 x A)
  | p ≡ q => (p.substitution2 x A) ≡ (q.substitution2 x A)
-- This is the old definition of substitution('alternative' document).

notation src "[" x "↦" A "]" => form.substitution2 src x A

inductive oform : Type
| atom : Nat → oform
| impl : oform → oform → oform
| neg : oform → oform
| id : oform → oform → oform
| free : oform

@[simp]
def subst (f : oform) (p : form) : form :=
  match f with
  | .atom m => .atom m
  | .impl s t => .impl (subst s p) (subst t p)
  | .neg s => .neg (subst s p)
  | .id s t => form.id (subst s p) (subst t p)
  | .free => p
-- This is the new definition of substitution ('valid' document).

inductive proof : form → Type
| ax1 : ∀ p q, proof (p ⇒i (q ⇒i p))
| ax2 : ∀ p q r, proof ((p ⇒i (q ⇒i r)) ⇒i ((p ⇒i q) ⇒i (p ⇒i r)))
| ax3 : ∀ p, proof (~~p ⇒i p)
| ax4 : ∀ p, proof (p ⇒i ~~p)
| ax5 : ∀ p q, proof ((~ p ⇒i ~ q) ⇒i (q ⇒i p))
| ax6 : ∀ p, proof (p ≡ p)
| ax7 : ∀ p q r, proof (((#p) ≡ q) ⇒i (r ⇒i r [p ↦ q ] ))
-- This is the old definition of the substitution axiom ('alternative' document)..
| ax7': ∀ p q f, proof ((p ≡ q) ⇒i (subst f p) ≡ (subst f q))
-- This is the new definition of the substitution axiom ('valid' document).
| mp : ∀ p q, proof p → proof (p ⇒i q) → proof q


inductive tV : Type
| one : tV
| two : tV
| three : tV

@[simp]
theorem test (a : tV) : a = tV.one ∨ a = tV.two ∨ a = tV.three := by
  cases a; repeat simp

inductive TRI (a : tV) : Prop :=
| one : a = tV.one → TRI a
| two : a = tV.two → TRI a
| three : a = tV.three → TRI a

theorem test' (a : tV) : TRI a := by
  cases a
  exact TRI.one rfl
  exact TRI.two rfl
  exact TRI.three rfl



@[simp]
theorem tV.one_ne_two : tV.one ≠ tV.two := by simp only [ne_eq, not_false_eq_true]

@[simp]
theorem tV.two_ne_one : tV.two ≠ tV.one := by simp only [ne_eq, not_false_eq_true]

@[simp]
theorem tV.one_ne_three : tV.one ≠ tV.three := by simp only [ne_eq, not_false_eq_true]

@[simp]
theorem tV.three_ne_one : tV.three ≠ tV.one := by simp only [ne_eq, not_false_eq_true]

@[simp]
theorem tV.two_ne_three : tV.two ≠ tV.three := by simp only [ne_eq, not_false_eq_true]

@[simp]
theorem tV.three_ne_two : tV.three ≠ tV.two := by simp only [ne_eq, not_false_eq_true]

inductive TRI_EQ (a b : tV) : Prop :=
| one_one : a = tV.one → b = tV.one → TRI_EQ a b
| two_two : a = tV.two → b = tV.two → TRI_EQ a b
| three_three : a = tV.three → b = tV.three → TRI_EQ a b

theorem tri_eq_case {a b : tV} (h : a = b): TRI_EQ a b := by
  cases a <;> cases b <;> simp at *
  exact TRI_EQ.one_one rfl rfl
  exact TRI_EQ.two_two rfl rfl
  exact TRI_EQ.three_three rfl rfl

structure model :=
  (interpretation : Nat → tV)

@[simp]
def tV.neg : tV → tV
  | tV.one => tV.two
  | _ => tV.one

@[simp]
def tV.impl : tV → tV → tV
  | tV.one, tV.two => tV.two
  | tV.one, tV.three => tV.two
  | _, _ => tV.one

@[simp]
def tV.id : tV → tV → tV
  | tV.one, tV.one => tV.one
  | tV.two, tV.two => tV.one
  | tV.three, tV.three => tV.one
  | _, _ => tV.three

@[simp]
def valuation (m : model) (p : form) : tV :=
  match p with
  | # n => m.interpretation n
  | p ⇒i q => tV.impl (valuation m p) (valuation m q)
  | ~ p => tV.neg (valuation m p)
  | p ≡ q => tV.id (valuation m p) (valuation m q)



theorem eq_val_id {m : model} {p q : form} (h₁: valuation m (p ≡ q) = tV.one) : (valuation m p) = (valuation m q) := by
  cases test' (valuation m p) <;> cases test' (valuation m q) <;> simp [*] at *
