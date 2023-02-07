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

/- Currently have no way of writing certain homs.
-- map f (corepr anything) ; counit : App F (Corepr _) -> App F (Radj F _ _)
-- map f (projComp (fst or snd)) ; counit : App F (X × _) -> App F (Radj F _ X) -/

inductive HomCorepr : {C : Cat} → CoreprObj C → Obj C → Type
  | coprod {C : Cat} {X Y Z : Obj C} (f : Hom X Z) (g : Hom Y Z) : HomCorepr (CoreprObj.Coprod X Y) Z
  | ladj {C D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj D} {Y : Obj C}
      (f : Hom X (App F Y)) : HomCorepr (CoreprObj.LAdj F H X) Y
  | botMk {C : Cat} {X : Obj C} : HomCorepr (CoreprObj.Bot C) X

inductive HomRepr : ∀ {C : Cat}, Obj C → ReprObj C → Type
  | prod {C : Cat} {X : Obj C} {Y Z : Obj C}
    (f : Hom X Y) (g : Hom X Z) : HomRepr X (ReprObj.Prod Y Z)
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

def ofEmb {C : Cat} {X Y : Obj C} (f : Emb X Y) : Hom X Y :=
  compEmb Hom.id f

def ofProj {C : Cat} {X Y : Obj C} (f : Proj X Y) : Hom X Y :=
  projComp f Hom.id

def inl {C : Cat} {X Y : Obj C} : Hom X (Coprod X Y) :=
  ofEmb Emb.inl

def inr {C : Cat} {X Y : Obj C} : Hom Y (Coprod X Y) :=
  ofEmb Emb.inr

def unit {C : Cat} {D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj D} : Hom X (App F (LAdj F H X)) :=
  ofEmb (Emb.unit F H)

def fst {C : Cat} {X Y : Obj C} : Hom (Prod X Y) X :=
  ofProj Proj.fst

def snd {C : Cat} {X Y : Obj C} : Hom (Prod X Y) Y :=
  ofProj Proj.snd

def counit {C : Cat} {D : Cat} (F : Func C D) (H : HasRAdj F) {X : Obj D} : Hom (App F (RAdj F H X)) X :=
  ofProj (Proj.counit F H)

@[match_pattern]
def botMk {C : Cat} {X : Obj C} : Hom (Bot C) X :=
  corepr HomCorepr.botMk

@[match_pattern]
def coprod {C : Cat} {X Y Z : Obj C} (f : Hom X Z) (g : Hom Y Z) : Hom (Coprod X Y) Z :=
  corepr (HomCorepr.coprod f g)

@[match_pattern]
def prod {C : Cat} {X Y Z : Obj C} (f : Hom X Y) (g : Hom X Z) : Hom X (Prod Y Z) :=
  repr (HomRepr.prod f g)

@[match_pattern]
def radj {C : Cat} {D : Cat} (F : Func C D) (H : HasRAdj F) {X : Obj C} {Y : Obj D} (f : Hom (App F X) Y) : Hom X (RAdj F H Y) :=
  repr (HomRepr.radj F H f)

@[match_pattern]
def ladj {C : Cat} {D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj C} {Y : Obj D} (f : Hom Y (App F X)) : Hom (LAdj F H Y) X :=
  corepr (HomCorepr.ladj F H f)

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
  | _, _, _, _, prod f g, projComp Proj.fst h => comp f h
  | _, _, _, _, prod f g, projComp Proj.snd h => comp g h
  | _, _, _, _, compEmb f Emb.inl, coprod g h => f.comp g
  | _, _, _, _, compEmb f Emb.inr, coprod g h => f.comp h
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

unsafe def ladjMap {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj D} (f : Hom X Y) :
    Hom (LAdj F H X) (LAdj F H Y) :=
  ladj _ _ (comp f (unit _ _))

unsafe def radjMap {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj D} (f : Hom X Y) :
    Hom (RAdj F H X) (RAdj F H Y) :=
  radj _ _ (comp (counit _ _) f)

def ladjPreserveBot {C D : Cat} (F : Func C D) (H : HasLAdj F) : Hom (LAdj F H (Obj.Bot _)) (Obj.Bot _) :=
  ladj _ _ botMk

def radjPreserveTop {C D : Cat} (F : Func C D) (H : HasRAdj F) : Hom (Obj.Top _) (RAdj F H (Obj.Top _)) :=
  radj _ _ topMk

unsafe def ladjPreserveCoprod {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj D} :
    Hom (LAdj F H (Obj.Coprod X Y)) (Obj.Coprod (LAdj F H X) (LAdj F H Y)) :=
  ladj _ _ (coprod (LAdjSymm _ H inl) (LAdjSymm _ H inr))

unsafe def ladjPreserveCoprodSymm {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj D} :
    Hom (Obj.Coprod (LAdj F H X) (LAdj F H Y)) (LAdj F H (Obj.Coprod X Y)) :=
  coprod (ladj _ _ (comp (unit F H) (map F (ladjMap _ _ inl))))
         (ladj _ _ (comp (unit F H) (map F (ladjMap _ _ inr))))

unsafe def radjPreserveProd {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj D} :
    Hom (Obj.Prod (RAdj F H X) (RAdj F H Y)) (RAdj F H (Obj.Prod X Y)) :=
  radj _ _ (prod (RAdjSymm _ H fst) (RAdjSymm _ H snd))

unsafe def radjPreserveProdSymm {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj D} :
    Hom (RAdj F H (Obj.Prod X Y)) (Obj.Prod (RAdj F H X) (RAdj F H Y)) :=
  prod (radj _ _ (comp (map F (radjMap _ _ fst)) (counit F H)))
       (radj _ _ (comp (map F (radjMap _ _ snd)) (counit F H)))

unsafe def preserveBotOfHasRAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) :
    Hom (App F (Obj.Bot _)) (Obj.Bot _):=
  RAdjSymm _ H botMk

unsafe def preserveTopOfHasLAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) :
    Hom (Obj.Top _) (App F (Obj.Top _)) :=
  LAdjSymm _ H topMk

unsafe def preserveCoprodOfHasRAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj C} :
    Hom (App F (Obj.Coprod X Y)) (Obj.Coprod (App F X) (App F Y)) :=
  RAdjSymm _ H (coprod (radj _ _ inl) (radj _ _ inr))

def preserveCoprodOfHasRAdjSymm {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj C} :
    Hom (Obj.Coprod (App F X) (App F Y)) (App F (Obj.Coprod X Y)) :=
  coprod (map F inl) (map F inr)

unsafe def preserveProdOfHasLAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj C} :
    Hom (Obj.Prod (App F X) (App F Y)) (App F (Obj.Prod X Y)) :=
  LAdjSymm _ H (prod (ladj _ _ fst) (ladj _ _ snd))

def preserveProdOfHasLAdjSymm {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj C} :
    Hom (App F (Obj.Prod X Y)) (Obj.Prod (App F X) (App F Y)) :=
  prod (map F fst) (map F snd)

section

unsafe def asCorepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C}, Hom (Corepr X) Y → HomCorepr X Y
  | _, _, _, Hom.corepr f => f
  | _, CoreprObj.Bot _, _, _ => HomCorepr.botMk
  | _, CoreprObj.Coprod X Y, _, f => HomCorepr.coprod (comp (ofEmb Emb.inl) f) (comp (ofEmb Emb.inr) f)
  | _, CoreprObj.LAdj F H X, _, f => HomCorepr.ladj _ _ (comp (ofEmb (Emb.unit F H)) (map F f))

unsafe def asRepr : ∀ {C : Cat} {X : Obj C} {Y : ReprObj C}, Hom X (Repr Y) → HomRepr X Y
  | _, _, _, Hom.repr f => f
  | _, _, ReprObj.Prod X Y, f => HomRepr.prod (comp f (ofProj Proj.fst)) (comp f (ofProj Proj.snd))
  | _, _, ReprObj.RAdj F H X, f => HomRepr.radj _ _ (comp (map F f) (ofProj (Proj.counit F H)))

end

instance : ∀ C : Cat, DecidableEq (Obj C) := sorry
instance : ∀ C : Cat, DecidableEq (CoreprObj C) := sorry
instance : ∀ C : Cat, DecidableEq (ReprObj C) := sorry
instance : ∀ C : Cat, ∀ X Y : Obj C, DecidableEq (Hom X Y) := sorry
instance : ∀ C : Cat, ∀ X : CoreprObj C, ∀ Y : Obj C, DecidableEq (HomCorepr X Y) := sorry
instance : ∀ C : Cat, ∀ X : Obj C, ∀ Y : ReprObj C, DecidableEq (HomRepr X Y) := sorry

mutual

/-
Normal forms
- If it can be written as `top_mk ; f` then it is. Uniqueness is fairly easy here.
- If it can be written as `f ; corepr_mk` then it is unless the first rule applies. What if there are two different ways of doing this?,
    Try to make sure `f` is not of that form
- If it can be written as `repr_mk ; f` then it is unless one of the first two rules apply.
- Not sure what else there is.
-/

open Hom

unsafe def getTopMkComp :
    ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Option (Hom (Obj.Top _) Y)
  | _, _, Obj.Top _, _ => some topMk
  | _, _, Obj.Var _ _, _ => none
  | _, X, _, repr (HomRepr.prod f g) =>
    match getTopMkComp f, getTopMkComp g with
    | some f', some g' => some (Hom.repr (HomRepr.prod f' g'))
    | _, _ => none
  | _, _, _, repr (HomRepr.radj F H f) =>
    match getTopMkComp f with
    | none => none
    | some f => some (radj F H (topMk.comp f))
  | _, _, Z, coprod f g =>
      match getTopMkComp f, getTopMkComp g with
      | some f, some g =>
          let nf := normalize f
          let ng := normalize g
          if nf = ng then nf else none
      | _, _ => none
  | _, _, _, ladj _ _ _ => none
  | _, _, _, Hom.map F f =>
    if hL : HasLAdj F
    then do return (LAdjSymm _ hL (comp topMk (← getTopMkComp f)))
    else none
  | _, _, _, projComp f g => getTopMkComp g
  | _, _, _, compEmb f g => do return (compEmb (← getTopMkComp f) g)
  | _, _, _, corepr HomCorepr.botMk => none
--What is shrinking?
unsafe def getCompCoprodBotMk :
    ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Option (Σ R : CoreprObj C, Hom X (Corepr R) × HomCorepr R Y)
  | _, Corepr (CoreprObj.Coprod X Y), _, f => some ⟨_, Hom.id, asCorepr f⟩
  | _, Corepr (CoreprObj.Bot _), _, f => some ⟨_, Hom.id, asCorepr f⟩
  | _, _, _, var _ => none
  | _, _, _, topMk => none
  | _, _, _, projComp f g =>
    match getCompCoprodBotMk g with
    | none => none
    | some ⟨R, g, h⟩ => some ⟨R, projComp f g , h⟩
  | _, _, _, compEmb f g =>
    match getCompCoprodBotMk f with
    | none => none
    | some ⟨R, f, h⟩ => some ⟨R, f, coreprComp h (ofEmb g)⟩
  | _, _, _, repr (HomRepr.prod f g) =>
    match getCompCoprodBotMk f, getCompCoprodBotMk g with
    | some ⟨R₁, f₁, f₂⟩, some ⟨R₂, g₁, g₂⟩ =>
        let nf := normalize f₁
        let ng := normalize g₁
        if hr : R₁ = R₂
          then if (hr ▸ nf) = ng
            then by
              subst R₁
              match R₂, nf, f₂, g₂ with
              | _, nf, HomCorepr.coprod f₂ f₃, HomCorepr.coprod g₂ g₃ =>
                exact some ⟨_, nf, HomCorepr.coprod (prod f₂ g₂) (prod f₃ g₃)⟩
              | _, nf, HomCorepr.botMk, HomCorepr.botMk => exact some ⟨_, nf, HomCorepr.botMk⟩
              | _, nf, HomCorepr.ladj _ _ _, _ => exact none
            else none
        else none
    | _, _ => none
  | _, _, _, Hom.repr (HomRepr.radj F H f) => none
  | _, _, _, map F f =>
    if hR : HasRAdj F
    then
      match getCompCoprodBotMk f with
      | none => none
      | some ⟨R, f, h⟩ =>
        match R, f, h with
        | _, f, HomCorepr.botMk => some ⟨_, comp (map F f) (preserveBotOfHasRAdj _ hR), HomCorepr.botMk⟩
        | _, f, HomCorepr.coprod g h =>
          some ⟨_, (map F f).comp (RAdjSymm _ hR (coprod (radj _ _ (ofEmb Emb.inl))
            (radj _ _ (ofEmb Emb.inr)))), HomCorepr.coprod (map F g) (map F h)⟩
        | _, _, _ => none
    else none
  | _, _, _, corepr (HomCorepr.ladj F H f) =>
    match getCompCoprodBotMk f with
    | none => none
    | some ⟨R, f, g⟩ =>
      match R, f, g with
        | _, f, HomCorepr.botMk => some ⟨_, ladj _ _ (comp f botMk), HomCorepr.botMk⟩
        | CoreprObj.Coprod X Y, f, HomCorepr.coprod g h =>
            some ⟨CoreprObj.Coprod (LAdj _ H X) (LAdj _ H Y),
              ladj F H (comp f (LAdjSymm _ H (ladjPreserveCoprod _ _))),
              HomCorepr.coprod (ladj _ _ g) (ladj _ _ h)⟩
        | _, _, _ => none

unsafe def getProdComp :
    ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Option (Σ A B : Obj C, Hom X A × Hom X B × Hom (Prod A B) Y)
  | _, _, Obj.Top _, f => none
  | _, Corepr (CoreprObj.Coprod X Y), _, f => none
  | _, Corepr (CoreprObj.Bot _), _, f => none
  | _, _, Obj.Repr (ReprObj.Prod X Y), f => some ⟨X, Y, comp f fst, comp f snd, Hom.id⟩
  | _, _, _, var _ => none
  | _, _, _, compEmb f g => _
  | _, _, _, _ => sorry

unsafe def normalize : ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Hom X Y := sorry

end

end Hom
