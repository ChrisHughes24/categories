import Mathlib.Init.Algebra.Order

set_option linter.unusedVariables false

class CatSystem (Cat : Type) :=
  [ decEq : DecidableEq Cat ]
  ( Func : Cat → Cat → Type )
  ( HasLAdj : ∀ (C D : Cat), Func C D → Prop )
  ( HasRAdj : ∀ (C D : Cat), Func C D → Prop )

/- We have a system of Categories -/
variable {Cat : Type} [CatSystem Cat]

attribute [instance] CatSystem.decEq

open CatSystem

--TODO : think about how adjoint preserve products.

mutual

inductive CoreprObj : Cat → Type
  | coprod {C : Cat} (X Y : Obj C) : CoreprObj C
  | LAdj (C D : Cat) (F : Func C D) : HasLAdj C D F → Obj D → CoreprObj C
  | bot : (C : Cat) → CoreprObj C

inductive ReprObj : Cat → Type
  | prod {C : Cat} : Obj C → Obj C → ReprObj C
  | RAdj (C D : Cat) (F : Func C D) : HasRAdj C D F → Obj D → ReprObj C

inductive Obj : Cat → Type
  | corepr : ∀ {C : Cat}, CoreprObj C → Obj C
  | var : (C : Cat) → ℕ → Obj C
  /- Below constructor should never be applied to product when `C ⥤ D` has a LAdj or
  to coproduct when `C ⥤ D` has a RAdj. -/
  | app : ∀ (C D : Cat), Func C D → Obj C → Obj D
  | repr : ∀ {C : Cat}, ReprObj C → Obj C
  | top : (C : Cat) → Obj C

end

/- Normal form inspired by rewriting procedure in appendix A of http://www.tac.mta.ca/tac/volumes/8/n5/n5.pdf
The exception to the rule being that the normal form of a map into `top` is always `top_mk` unless the
map is from `bot`. -/

open Obj

nonrec def Obj.coprod {C : Cat} (X Y : Obj C) : Obj C :=
  corepr (CoreprObj.coprod X Y)

@[match_pattern]
nonrec def Obj.prod {C : Cat} (X Y : Obj C) : Obj C :=
  Obj.repr (ReprObj.prod X Y)

nonrec def Obj.LAdj (C D : Cat) (F : Func C D) (H : HasLAdj C D F) (X : Obj D) : Obj C :=
  corepr (CoreprObj.LAdj C D F H X)

nonrec def Obj.RAdj (C D : Cat) (F : Func C D) (H : HasRAdj C D F) (X : Obj D) : Obj C :=
  Obj.repr (ReprObj.RAdj C D F H X)

nonrec def Obj.bot (C : Cat) : Obj C :=
  corepr (CoreprObj.bot C)

inductive Emb {C : Cat} : Obj C → Obj C → Type
| inl : ∀ {X Y : Obj C}, Emb X (coprod X Y)
| inr : ∀ {X Y : Obj C}, Emb Y (coprod X Y)
| unit : ∀ {D : Cat} (F : Func D C) (H : HasLAdj D C F) {X : Obj C},
    Emb X (app D C F (LAdj D C F H X))

inductive Proj {C : Cat} : Obj C → Obj C → Type
| fst : ∀ {X Y : Obj C}, Proj (prod X Y) X
| snd : ∀ {X Y : Obj C}, Proj (prod X Y) Y
| counit : ∀ {D : Cat} (F : Func D C) (H : HasRAdj D C F) {X : Obj C},
    Proj (app D C F (RAdj D C F H X)) X

mutual

inductive HomCorepr : {C : Cat} → CoreprObj C → Obj C → Type
  | coprod {C : Cat} {X Y Z : Obj C} (f : Hom X Z) (g : Hom Y Z) : HomCorepr (CoreprObj.coprod X Y) Z
  | ladj {C D : Cat} (F : Func C D) (H : HasLAdj C D F) {X : Obj D} {Y : Obj C}
      (f : Hom X (app C D F Y)) : HomCorepr (CoreprObj.LAdj C D F H X) Y
  | bot {C : Cat} {X : Obj C} : HomCorepr (CoreprObj.bot C) X

inductive HomRepr : ∀ {C : Cat}, Obj C → ReprObj C → Type
  /-- Never to be used when `f` and `g` are of the form `f = f₁ ; f₂`, `g = g₁ ; g₂` and
  `f₁ = g₁` -/
  | prod {C : Cat} {X : Obj C} {Y Z : Obj C}
    (f : Hom X Y) (g : Hom X Z) : HomRepr X (ReprObj.prod Y Z)
  /-- Never to be used when `f` is a composition. -/
  | radj {C D : Cat} (F : Func C D) (H : HasRAdj C D F) {X : Obj C} {Y : Obj D}
    (f : Hom (app C D F X) Y) : HomRepr X (ReprObj.RAdj C D F H Y)

/-- Cut eliminated homs. Maybe change to not cut eliminated. -/
inductive Hom : {C : Cat} → Obj C → Obj C → Type
  | projComp : ∀ {C : Cat} {X Y Z : Obj C} (f : Proj X Y) (g : Hom Y Z), Hom X Z
  | CompEmb : ∀ {C : Cat} {X : Obj C} {Y Z : Obj C}
      (f : Hom X Y) (g : Emb Y Z), Hom X Z
  | var : ∀ {C : Cat} {X Y : ℕ} (n : ℕ), Hom (var C X) (var C Y)
  | id : ∀ {C : Cat} (X : Obj C), Hom X X
  | topMk : ∀ {C : Cat} {X : Obj C}, Hom X (top C)
  | map : ∀ {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj C}
      (f : Hom X Y), Hom (app C D F X) (app C D F Y)
  | corepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C} (f : HomCorepr X Y), Hom (corepr X) Y
  | repr : ∀ {C : Cat} {X : Obj C} {Y : ReprObj C} (f : HomRepr X Y),
      Hom X (repr Y)

end

/-
Normal forms
- If it can be written as `top_mk ; f` then it is.
- If it can be written as `f ; corepr_mk` then it is unless the first rule applies.
- If it can be written as `repr_mk ; f` then it is unless one of the first two rules apply.
- Not sure what else there is.
-/
open Hom

mutual

def coreprComp : ∀ {C : Cat} {X : CoreprObj C} {Y Z : Obj C}, HomCorepr X Y → Hom Y Z → HomCorepr X Z
  | _, _, _, _, HomCorepr.coprod f g, h => HomCorepr.coprod (comp f h) (comp g h)
  | _, _, _, _, HomCorepr.ladj F H f, g => HomCorepr.ladj _ _ (comp f (Hom.map F g))
  | _, _, _, _, HomCorepr.bot, _ => HomCorepr.bot

def compRepr : ∀ {C : Cat} {X Y : Obj C} {Z : ReprObj C}, Hom X Y → HomRepr Y Z → HomRepr X Z
  | _, _, _, _, f, HomRepr.prod g h => HomRepr.prod (comp f g) (comp f h)
  | _, _, _, _, f, HomRepr.radj F H g => HomRepr.radj _ _ (comp (Hom.map F f) g)

def comp : ∀ {C : Cat} {X Y Z : Obj C}, Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, _, Hom.corepr f, g => corepr (coreprComp f g)
  | _, _, _, _, f, Hom.repr g => repr (compRepr f g)
  | _, _, _, _, Hom.id _, f => f
  | _, _, _, _, f, Hom.id _ => f
  | _, _, _, _, _, _ => sorry
  --| _, _, _, _, _, _ => sorry
  --| _, _, _, _, _, _ => sorry
  --| _, _, _, _, _, _ => sorry
  --| _, _, _, _, _, _ => sorry

end

section

open Hom

/-- We assume that naturality has been applied as much as possible. -/
def getTopMkComp : ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Option (Hom (Obj.top _) Y)
  | _, _, _, Hom.topMk => some topMk
  | _, X, Obj.prod Y Z, Hom.repr (HomRepr.prod f g) =>
    match getTopMkComp f, getTopMkComp g with
    | none, _ => none
    | _, none => none
    | some f, some g => some (Hom.repr (HomRepr.prod f g))
  | _, _, _, Hom.repr (HomRepr.radj F h f) =>
    match getTopMkComp f with
    | none => none
    | some f => some (Hom.repr (HomRepr.radj F h (_ /-top_mk ∘ f-/)))
  | _, _, _, _ => sorry

end
