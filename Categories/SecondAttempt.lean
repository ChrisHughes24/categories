import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Notation

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
deriving DecidableEq

inductive Proj {C : Cat} : Obj C → Obj C → Type
  | fst : ∀ {X Y : Obj C}, Proj (prod X Y) X
  | snd : ∀ {X Y : Obj C}, Proj (prod X Y) Y
  | counit : ∀ {D : Cat} (F : Func D C) (H : HasRAdj D C F) {X : Obj C},
      Proj (app D C F (RAdj D C F H X)) X

inductive HomVar (C : Cat) : (X Y : ℕ) → Type
  | id : ∀ (X : ℕ), HomVar C X X
  | varComp {X Y Z : ℕ} (n : ℕ) (f : HomVar C Y Z) : HomVar C X Z

def HomVar.comp {C : Cat} : ∀ {X Y Z : ℕ} (f : HomVar C X Y) (g : HomVar C Y Z), HomVar C X Z
  | _, _, _, HomVar.id _, f => f
  | _, _, _, HomVar.varComp n f, g => HomVar.varComp n (HomVar.comp f g)

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
  | compEmb : ∀ {C : Cat} {X : Obj C} {Y Z : Obj C}
      (f : Hom X Y) (g : Emb Y Z), Hom X Z
  | var : ∀ {C : Cat} {X Y : ℕ}, HomVar C X Y → Hom (var C X) (var C Y)
  | topMk : ∀ {C : Cat} {X : Obj C}, Hom X (top C)
  | map : ∀ {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj C}
      (f : Hom X Y), Hom (app C D F X) (app C D F Y)
  | corepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C} (f : HomCorepr X Y), Hom (corepr X) Y
  | repr : ∀ {C : Cat} {X : Obj C} {Y : ReprObj C} (f : HomRepr X Y),
      Hom X (repr Y)

end


namespace Hom

mutual

unsafe def coreprComp : ∀ {C : Cat} {X : CoreprObj C} {Y Z : Obj C}, HomCorepr X Y → Hom Y Z → HomCorepr X Z
  | _, _, _, _, HomCorepr.coprod f g, h => HomCorepr.coprod (comp f h) (comp g h)
  | _, _, _, _, HomCorepr.ladj F H f, g => HomCorepr.ladj _ _ (comp f (Hom.map F g))
  | _, _, _, _, HomCorepr.bot, _ => HomCorepr.bot

unsafe def compRepr : ∀ {C : Cat} {X Y : Obj C} {Z : ReprObj C}, Hom X Y → HomRepr Y Z → HomRepr X Z
  | _, _, _, _, f, HomRepr.prod g h => HomRepr.prod (comp f g) (comp f h)
  | _, _, _, _, f, HomRepr.radj F H g => HomRepr.radj _ _ (comp (Hom.map F f) g)

unsafe def comp : ∀ {C : Cat} {X Y Z : Obj C}, Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, _, _, topMk => topMk
  | _, _, _, _, Hom.corepr f, g => corepr (coreprComp f g)
  | _, _, _, _, f, Hom.repr g => repr (compRepr f g)
  | _, _, _, _, Hom.projComp f g, h => Hom.projComp f (comp g h)
  | _, _, _, _, f, Hom.compEmb g h => compEmb (f.comp g) h
  | _, _, _, _, Hom.repr (HomRepr.prod f g), projComp Proj.fst h => comp f h
  | _, _, _, _, Hom.repr (HomRepr.prod f g), projComp Proj.snd h => comp g h
  | _, _, _, _, map _ _, map _ _ => sorry
  | _, _, _, _, map _ _ , projComp (Proj.counit _ _) _=> sorry
  | _, _, _, _, var f, var g => var (f.comp g)
  | _, _, _, _, compEmb f Emb.inl, corepr (HomCorepr.coprod g h) => f.comp g
  | _, _, _, _, compEmb f Emb.inr, corepr (HomCorepr.coprod g h) => f.comp h
  | _, _, _, _, compEmb _ _, map _ _ => sorry
  --| _, _, _, _, _, _ => sorry
  --| _, _, _, _, _, _ => sorry
  --| _, _, _, _, _, _ => sorry
  --| _, _, _, _, _, _ => sorry

end

section

mutual

/-
Normal forms
- If it can be written as `top_mk ; f` then it is.
- If it can be written as `f ; corepr_mk` then it is unless the first rule applies.
- If it can be written as `repr_mk ; f` then it is unless one of the first two rules apply.
- Not sure what else there is.
-/

open Hom

/-- We assume that naturality has been applied as much as possible. -/
unsafe def getTopMkComp [∀ C : Cat, ∀ X Y : Obj C, DecidableEq (Hom X Y)] :
    ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Option (Hom (Obj.top _) Y)
  | _, _, _, Hom.topMk => some topMk
  | _, X, Obj.prod Y Z, Hom.repr (HomRepr.prod f g) =>
    match getTopMkComp f, getTopMkComp g with
    | none, _ => none
    | _, none => none
    | some f, some g => some (Hom.repr (HomRepr.prod f g))
  | _, _, _, Hom.repr (HomRepr.radj F h f) =>
    match getTopMkComp f with
    | none => none
    | some f => some (Hom.repr (HomRepr.radj F h (topMk.comp f)))
  | _, _, Z, Hom.corepr (HomCorepr.coprod f g) =>
      match getTopMkComp f, getTopMkComp g with
      | none, _ => none
      | _, none => none
      | some f, some g =>
        let nf := normalize f
        let ng := normalize g
        if nf = ng
          then nf
          else none
  | _, _, Z, Hom.corepr (HomCorepr.ladj F H f) =>
    match getTopMkComp f with
    | none => none
    | some f => some (Hom.comp _ (Hom.corepr (HomCorepr.ladj F H f)))

  | _, _, _, _ => sorry

unsafe def normalize : ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Hom X Y := sorry

end

end Hom

end

end
end Hom