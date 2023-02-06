import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Notation

set_option linter.unusedVariables false

class CatSystem (Cat : Type) :=
  [ decEq : DecidableEq Cat ]
  ( Func : Cat → Cat → Type )
  ( HasLAdj : ∀ {C D : Cat}, Func C D → Prop )
  [ decidableLAdj : ∀ (C D : Cat) (F : Func C D), Decidable (HasLAdj F) ]
  ( HasRAdj : ∀ {C D : Cat}, Func C D → Prop )
  [ decidableRAdj : ∀ (C D : Cat) (F : Func C D), Decidable (HasRAdj F) ]

/- We have a system of Categories -/
variable {Cat : Type} [CatSystem Cat]

attribute [instance] CatSystem.decEq CatSystem.decidableLAdj CatSystem.decidableRAdj

open CatSystem

--TODO : think about how adjoint preserve products.

mutual

inductive CoreprObj : Cat → Type
  | Coprod {C : Cat} (X Y : Obj C) : CoreprObj C
  | LAdj {C D : Cat} (F : Func C D) : HasLAdj F → Obj D → CoreprObj C
  | Bot : (C : Cat) → CoreprObj C

inductive ReprObj : Cat → Type
  | Prod {C : Cat} : Obj C → Obj C → ReprObj C
  | RAdj {C D : Cat} (F : Func C D) : HasRAdj F → Obj D → ReprObj C

inductive Obj : Cat → Type
  | Corepr : ∀ {C : Cat}, CoreprObj C → Obj C
  | Var : (C : Cat) → ℕ → Obj C
  | App : ∀ {C D : Cat}, Func C D → Obj C → Obj D
  | Repr : ∀ {C : Cat}, ReprObj C → Obj C
  | Top : (C : Cat) → Obj C

end

open Obj

@[match_pattern]
nonrec def Obj.Coprod {C : Cat} (X Y : Obj C) : Obj C :=
  Corepr (CoreprObj.Coprod X Y)

@[match_pattern]
nonrec def Obj.Prod {C : Cat} (X Y : Obj C) : Obj C :=
  Obj.Repr (ReprObj.Prod X Y)

@[match_pattern]
nonrec def Obj.LAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) (X : Obj D) : Obj C :=
  Corepr (CoreprObj.LAdj F H X)

@[match_pattern]
nonrec def Obj.RAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) (X : Obj D) : Obj C :=
  Obj.Repr (ReprObj.RAdj F H X)

@[match_pattern]
nonrec def Obj.Bot (C : Cat) : Obj C :=
  Corepr (CoreprObj.Bot C)

inductive HomVar (C : Cat) : (X Y : ℕ) → Type
  | id : ∀ (X : ℕ), HomVar C X X
  | varComp {X Y Z : ℕ} (n : ℕ) (f : HomVar C Y Z) : HomVar C X Z
  deriving DecidableEq

def HomVar.comp {C : Cat} : ∀ {X Y Z : ℕ} (f : HomVar C X Y) (g : HomVar C Y Z), HomVar C X Z
  | _, _, _, HomVar.id _, f => f
  | _, _, _, HomVar.varComp n f, g => HomVar.varComp n (HomVar.comp f g)

inductive Emb : ∀ {C : Cat}, Obj C → Obj C → Type
  | inl : ∀ {X Y : Obj C}, Emb X (Coprod X Y)
  | inr : ∀ {X Y : Obj C}, Emb Y (Coprod X Y)
  | unit : ∀ {D : Cat} (F : Func D C) (H : HasLAdj F) {X : Obj C}, Emb X (App F (LAdj F H X))

inductive Proj : ∀ {C : Cat}, Obj C → Obj C → Type
  | fst : ∀ {X Y : Obj C}, Proj (Prod X Y) X
  | snd : ∀ {X Y : Obj C}, Proj (Prod X Y) Y
  | counit : ∀ {D : Cat} (F : Func D C) (H : HasRAdj F) {X : Obj C},
      Proj (App F (RAdj F H X)) X

mutual

/- Currently have no way of writing certain homs.  -/

inductive HomCorepr : {C : Cat} → CoreprObj C → Obj C → Type
  | coprod {C : Cat} {X Y Z : Obj C} (f : Hom X Z) (g : Hom Y Z) : HomCorepr (CoreprObj.Coprod X Y) Z
  | ladj {C D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj D} {Y : Obj C}
      (f : Hom X (App F Y)) : HomCorepr (CoreprObj.LAdj F H X) Y
  | botMk {C : Cat} {X : Obj C} : HomCorepr (CoreprObj.Bot C) X

inductive HomRepr : ∀ {C : Cat}, Obj C → ReprObj C → Type
  /-- Never to be used when `f` and `g` are of the form `f = f₁ ; f₂`, `g = g₁ ; g₂` and
  `f₁ = g₁` -/
  | prod {C : Cat} {X : Obj C} {Y Z : Obj C}
    (f : Hom X Y) (g : Hom X Z) : HomRepr X (ReprObj.Prod Y Z)
  /-- Never to be used when `f` is a composition. -/
  | radj {C D : Cat} (F : Func C D) (H : HasRAdj F) {X : Obj C} {Y : Obj D}
    (f : Hom (App F X) Y) : HomRepr X (ReprObj.RAdj F H Y)

inductive Hom : ∀ {C : Cat}, Obj C → Obj C → Type
  | projComp : ∀ {C : Cat} {X Y Z : Obj C} (f : Proj X Y) (g : Hom Y Z), Hom X Z
  | compEmb : ∀ {C : Cat} {X : Obj C} {Y Z : Obj C} (f : Hom X Y) (g : Emb Y Z), Hom X Z
  | topMk : ∀ {C : Cat} {X : Obj C}, Hom X (Top C)
  | corepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C} (f : HomCorepr X Y), Hom (Corepr X) Y
  | repr : ∀ {C : Cat} {X : Obj C} {Y : ReprObj C} (f : HomRepr X Y),
      Hom X (Repr Y)
  | map : ∀ {C D : Cat} {X Y : Obj C} (F : Func C D) (f : Hom X Y), Hom (App F X) (App F Y)
  | var : ∀ {C : Cat} {X Y : ℕ}, HomVar C X Y → Hom (Var C X) (Var C Y)

end

namespace Hom

def id : ∀ {C : Cat} {X : Obj C}, Hom X X
  | _, Obj.Var C X => Hom.var (HomVar.id _)
  | _, Obj.Top C => Hom.topMk
  | _, Obj.App F X => Hom.map F Hom.id
  | _, Obj.Repr (ReprObj.Prod X Y) => repr (HomRepr.prod (Hom.projComp Proj.fst Hom.id) (Hom.projComp Proj.snd Hom.id))
  | _, Obj.Repr (ReprObj.RAdj F H Y) => repr (HomRepr.radj F H (Hom.projComp (Proj.counit F H) Hom.id))
  | _, Obj.Corepr (CoreprObj.Coprod X Y) => corepr (HomCorepr.coprod (Hom.compEmb Hom.id Emb.inl) (Hom.compEmb Hom.id Emb.inr))
  | _, Obj.Corepr (CoreprObj.LAdj F H X) => corepr (HomCorepr.ladj F H (Hom.compEmb Hom.id (Emb.unit F H)))
  | _, Obj.Corepr (CoreprObj.Bot C) => corepr HomCorepr.botMk

mutual

unsafe def coreprComp : ∀ {C : Cat} {X : CoreprObj C} {Y Z : Obj C}, HomCorepr X Y → Hom Y Z → HomCorepr X Z
  | _, _, _, _, HomCorepr.coprod f g, h => HomCorepr.coprod (comp f h) (comp g h)
  | _, _, _, _, HomCorepr.ladj F H f, g => HomCorepr.ladj _ _ (comp f (Hom.map F g))
  | _, _, _, _, HomCorepr.botMk, _ => HomCorepr.botMk

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
  | _, _, _, _, compEmb f Emb.inl, corepr (HomCorepr.coprod g h) => f.comp g
  | _, _, _, _, compEmb f Emb.inr, corepr (HomCorepr.coprod g h) => f.comp h
  | _, _, _, _, var f, var g => var (HomVar.comp f g)
  | _, _, _, _, map F f, map _ g => map _ (comp f g)
  --| _, App F X, _, _, map _ (projComp _ _), projComp (Proj.counit _ _) _ => sorry  --Leave it
  --   cases f

  -- -- | _, _, _, _, compEmb _ _, map _ _ => sorry
  | _, _, _, _, _, _ => sorry

end

unsafe def LAdjSymm {C D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj D} {Y : Obj C}
    (f : Hom (Obj.LAdj F H X) Y) : Hom X (App F Y) :=
  Hom.comp (Hom.compEmb Hom.id (Emb.unit _ H)) (map F f)

unsafe def RAdjSymm {C D : Cat} (F : Func C D) (H : HasRAdj F) {X : Obj C} {Y : Obj D}
    (f : Hom X (Obj.RAdj F H Y)) : Hom (App F X) Y :=
  Hom.comp (map F f) (Hom.projComp (Proj.counit _ H) Hom.id)

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

unsafe def getTopMkComp [∀ C : Cat, ∀ X Y : Obj C, DecidableEq (Hom X Y)] :
    ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Option (Hom (Obj.Top _) Y)
  | _, _, Obj.Top _, _ => some topMk
  | _, _, Obj.Var _ _, _ => none
  | _, X, _, Hom.repr (HomRepr.prod f g) =>
    match getTopMkComp f, getTopMkComp g with
    | some f', some g' => some (Hom.repr (HomRepr.prod f' g'))
    | _, _ => none
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
  | _, _, _, Hom.corepr (HomCorepr.ladj F H f) => none
  | _, _, _, Hom.map F f =>
    if hR : HasLAdj F
    then
      match getTopMkComp f with
      | none => none
      | some f => some $ LAdjSymm _ hR (comp topMk f)
    else none
  | _, _, _, projComp f g => getTopMkComp g
  | _, _, _, compEmb f g =>
    match getTopMkComp f with
    | none => none
    | some f => compEmb f g
  | _, _, _, corepr HomCorepr.botMk => none

unsafe def normalize : ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Hom X Y := sorry

end

end Hom
