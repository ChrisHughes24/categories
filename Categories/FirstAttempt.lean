import Mathlib.Tactic.Have
/-
I will make a partially ordered collection of categories, with functors between them.
There will be assumptions about which of these have left/right adjoints.

-/



structure Cat : Type :=
  ( name : String )
deriving DecidableEq

structure FuncVar (C D : Cat) : Type :=
  (name : String)
deriving DecidableEq

inductive Func : Cat → Cat → Type
  | id (C : Cat) : Func C C
  | comp' {C D E : Cat} : FuncVar C D → Func D E → Func C E
  deriving DecidableEq

def FuncVar.toFunc {C D : Cat} (F : FuncVar C D) : Func C D :=
  Func.comp' F $ Func.id _

def Func.comp : {C D E : Cat} → Func C D → Func D E → Func C E
  | _, _, _, Func.id _, G => G
  | _, _, _, Func.comp' F G, H => Func.comp' F (comp G H)

structure FData : Type :=
  ( rel {C D : Cat} : Func C D → Func C D → Prop )
  [ decidRel {C D : Cat} : DecidableRel (@rel C D) ]
  ( refl {C D : Cat} (F : Func C D) : rel F F )
  ( symm {C D : Cat} {F G : Func C D} : rel G F → rel F G )
  ( trans {C D : Cat} {F G H : Func C D} : rel F G → rel G H → rel F H )
  ( rel_comp {C D E : Cat} {F₁ F₂ : Func C D} {G₁ G₂ : Func D E} :
    rel F₁ F₂ → rel G₁ G₂ → rel (F₁.comp G₁) (F₂.comp G₂) )
  ( hasRAdj {C D : Cat} : Func C D → Prop )
  [ decidHasRAdj {C D : Cat} (F : Func C D): Decidable (hasRAdj F) ]
  ( hasRAdjCompLeft {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
    rel F (G.comp H) → hasRAdj F → hasRAdj G )
  ( hasRAdjCompRight {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
    rel F (G.comp H) → hasRAdj F → hasRAdj H )
  ( hasLAdj {C D : Cat} : Func C D → Prop )
  [ decidHasLAdj {C D : Cat} (F : Func C D): Decidable (hasLAdj F) ]
  ( hasLAdjCompLeft {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
    rel F (G.comp H) → hasLAdj F → hasLAdj G )
  ( hasLAdjCompRight {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
    rel F (G.comp H) → hasLAdj F → hasLAdj H )

attribute [instance] FData.decidRel FData.decidHasRAdj FData.decidHasLAdj

def FuncVar.hasRAdj {C D : Cat} (d : FData) (F : FuncVar C D) : Prop :=
  d.hasRAdj F.toFunc

instance {C D : Cat} (d : FData) (F : FuncVar C D) : Decidable (F.hasRAdj d) :=
  d.decidHasRAdj _

def FuncVar.hasLAdj {C D : Cat} (d : FData) (F : FuncVar C D) : Prop :=
  d.hasLAdj F.toFunc

instance {C D : Cat} (d : FData) (F : FuncVar C D) : Decidable (F.hasLAdj d) :=
  d.decidHasLAdj _

inductive Obj (d : FData) : Cat → Type
  | Ovar : String → Obj d C
  | prod : Obj d C → Obj d C → Obj d C
  | coprod : Obj d C → Obj d C → Obj d C
  | app {C D : Cat} : FuncVar C D → Obj d C → Obj d D
  | rAdjApp {C D : Cat} (F : FuncVar C D) : F.hasRAdj d → Obj d D → Obj d C
  | lAdjApp {C D : Cat} (F : FuncVar C D) : F.hasLAdj d → Obj d D → Obj d C
  | top : Obj d C
  | bot : Obj d C
deriving DecidableEq

namespace Obj

variable {d : FData}

def syn : {C : Cat} → (X Y : Obj d C) → Type
| _, _, top => Unit
| _, bot, _ => Unit
| _, X, prod Y Z => syn X Z × syn Y Z
| _, X, rAdjApp F _ Y => syn (app F X) Y

