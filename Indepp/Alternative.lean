import MIL.Independencep.definition
import MIL.Independencep.valid

@[reducible]






def tV.ax1 (p q :tV) : tV.impl p (tV.impl q p) = tV.one
  := by cases p; cases q; repeat rfl

def tV.ax2 (p q r : tV) : tV.impl (tV.impl p (tV.impl q r)) (tV.impl (tV.impl p q) (tV.impl p r)) = tV.one
  := by cases p; cases q; cases r; repeat rfl

def tV.ax3 (p : tV) : tV.impl (tV.neg (tV.neg p)) p = tV.one
  := by cases p; repeat rfl

def tV.ax4 (p : tV) : tV.impl p (tV.neg (tV.neg p)) = tV.one
  := by cases p; repeat rfl
#check tV.ax4

def tV.ax5 (p q : tV) : tV.impl (tV.impl (tV.neg p) (tV.neg q)) (tV.impl q p) = tV.one
  := by cases p; cases q; repeat rfl; repeat cases q; repeat rfl

def tV.ax6 (p : tV) : tV.id p p = tV.one
  := by cases p; repeat rfl

-- def tV.ax7 (p q r : tV) :
--   tV.impl (tV.impl p q) (tV.impl r (form.substitution2 r n q )) = tV.one
--   := by cases p; cases q; cases r; repeat rfl; repeat cases r; repeat rfl

def id.ax7 (p q : Nat) (r : form)(h : p = q): r[p ↦ (#q) ] = r:=
    by
    rw [h]
    induction r with
    | atom n => unfold form.substitution2
                cases em (q=n) with
                | inl h1 => simp [h1]
                | inr h2 => simp [h2]
    | impl a b => unfold form.substitution2
                  rename_i h1 h2
                  rw [h1,h2]
    | neg a b => unfold form.substitution2
                 rw [b]
    | id a b => unfold form.substitution2
                rename_i h1 h2
                rw [h1,h2]









def sub5lemma(p q :tV)(h: p = q): tV.impl p q = tV.one :=
    by
    rw [h]
    cases q; repeat rfl; repeat cases q; repeat rfl


def sat.ax7 (p : Nat) (q r: form) (m : model) (h : valuation m (#p) = valuation m q):
     ((valuation m r) =  (valuation m (r[p ↦ q ]))):= by
      cases test' (valuation m (form.substitution2 r p q)) <;> cases test' (valuation m r) <;>
      simp [*] at *











def sublemma (p q :tV):
  tV.impl (tV.id p q) (tV.impl p q) = tV.one
  := by cases p; cases q; repeat rfl; repeat cases q; repeat rfl

def reflemma (n: tV): tV.impl n n = tV.one
  := by cases n; repeat rfl

def idlemma (p :tV):
  tV.impl p tV.one = tV.one:= by cases p; repeat rfl

def subsublemma (p q n:tV):
  tV.impl (tV.id p q) (tV.impl n n) = tV.one
  :=
  by rw [reflemma]
     rw [idlemma]


def subsubsublemma (p q : tV)(h: ¬(p = tV.one)) : tV.impl p q = tV.one :=
    by
    unfold tV.impl
    simp [h]

def sub4lemma (p q : tV)(h1: (p = tV.one))(h2: (q = tV.one)) : tV.impl p q = tV.one :=
    by
    rw [h1,h2]
    rfl
















def model.valid (p : form) : Prop :=
∀ m, valuation m p = tV.one


theorem ax1_valid : ∀ p q, model.valid (p ⇒i (q ⇒i p)) :=
by
intro _ _ _
apply tV.ax1

theorem ax2_valid : ∀ p q r, model.valid ((p ⇒i (q ⇒i r)) ⇒i ((p ⇒i q) ⇒i (p ⇒i r))) :=
by
intro _ _ _ _
apply tV.ax2


theorem ax3_valid : ∀ p, model.valid ((~(~p)) ⇒i p) :=
by
intro p1 m
apply tV.ax3


theorem ax4_valid : ∀ p, model.valid (p ⇒i ~~p) :=
by
intro _ _
apply tV.ax4


theorem ax5_valid : ∀ p q, model.valid (((~ p) ⇒i (~ q)) ⇒i (q ⇒i p)) :=
by
intro _ _ _
apply tV.ax5

theorem ax6_valid : ∀ p, model.valid (p ≡ p) :=
by
intro _ _
apply tV.ax6
#check tV.ax6


theorem ax7_valid : ∀ p q r, model.valid (((#p) ≡ q) ⇒i (r ⇒i r [p ↦ q ] )) :=
by
intro p q r m
unfold valuation
cases em ((valuation m ((#p)≡q)) = tV.one) with
| inr h => exact subsubsublemma (valuation m ((#p)≡q)) (valuation m (r⇒ir[p↦q])) h
| inl h => have h4 : (valuation m (#p) = valuation m (q)) := by sorry
           rw [h]
           apply sub4lemma
           rfl
           have h5:_ := sat.ax7 p q r m h4
           apply sub5lemma
           assumption
