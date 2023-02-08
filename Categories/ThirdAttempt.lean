import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Tactic.Linarith

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
  | Top : (C : Cat) → ReprObj C

inductive Obj : Cat → Type
  | Corepr : ∀ {C : Cat}, CoreprObj C → Obj C
  | Var : (C : Cat) → ℕ → Obj C
  | App : ∀ {C D : Cat}, Func C D → Obj C → Obj D
  | Repr : ∀ {C : Cat}, ReprObj C → Obj C

end

@[simp]
def Obj.size : ∀ {C : Cat} (X : Obj C), ℕ
  | _, Obj.Corepr (CoreprObj.Coprod X Y) => 1 + Obj.size X + Obj.size Y
  | _, Obj.Corepr (CoreprObj.LAdj F H X) => 2 + Obj.size X
  | _, Obj.Corepr (CoreprObj.Bot C) => 1
  | _, Obj.Var C n => 1
  | _, Obj.App F X => 1 + Obj.size X
  | _, Obj.Repr (ReprObj.Prod X Y) => 1 + Obj.size X + Obj.size Y
  | _, Obj.Repr (ReprObj.RAdj F H X) => 2 + Obj.size X
  | _, Obj.Repr (ReprObj.Top C) => 1

open Obj

@[match_pattern, simp]
nonrec def Obj.Coprod {C : Cat} (X Y : Obj C) : Obj C :=
  Corepr (CoreprObj.Coprod X Y)

@[match_pattern, simp]
nonrec def Obj.Prod {C : Cat} (X Y : Obj C) : Obj C :=
  Obj.Repr (ReprObj.Prod X Y)

@[match_pattern, simp]
nonrec def Obj.LAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) (X : Obj D) : Obj C :=
  Corepr (CoreprObj.LAdj F H X)

@[match_pattern, simp]
nonrec def Obj.RAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) (X : Obj D) : Obj C :=
  Obj.Repr (ReprObj.RAdj F H X)

@[match_pattern]
nonrec def Obj.Bot (C : Cat) : Obj C :=
  Corepr (CoreprObj.Bot C)

@[match_pattern]
nonrec def Obj.Top (C : Cat) : Obj C :=
  Obj.Repr (ReprObj.Top C)

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
  deriving DecidableEq

inductive Proj : ∀ {C : Cat}, Obj C → Obj C → Type
  | fst : ∀ {X Y : Obj C}, Proj (Prod X Y) X
  | snd : ∀ {X Y : Obj C}, Proj (Prod X Y) Y
  | counit : ∀ {D : Cat} (F : Func D C) (H : HasRAdj F) {X : Obj C},
      Proj (App F (RAdj F H X)) X
  deriving DecidableEq

theorem size_lt_of_emb {C : Cat} {X Y : Obj C} (f : Emb X Y) : Obj.size X < Obj.size Y := by
  cases f <;> simp [add_comm] <;> linarith

theorem size_lt_of_proj {C : Cat} {X Y : Obj C} (f : Proj X Y) : Obj.size Y < Obj.size X := by
  cases f <;> simp <;> linarith

mutual

/- Currently have no way of writing certain homs.
-- map F (corepr anything) ; counit : App F (Corepr _) -> App F (Radj F _ _)
-- map F (projComp (fst or snd)) ; counit : App F (X × _) -> App F (Radj F _ X) -/

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
  | topMk {C : Cat} {X : Obj C} : HomRepr X (ReprObj.Top C)

inductive Hom : ∀ {C : Cat}, Obj C → Obj C → Type
  | projComp : ∀ {C : Cat} {X Y Z : Obj C} (f : Proj X Y) (g : Hom Y Z), Hom X Z
  | compEmb : ∀ {C : Cat} {X : Obj C} {Y Z : Obj C} (f : Hom X Y) (g : Emb Y Z), Hom X Z
  | corepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C} (f : HomCorepr X Y), Hom (Corepr X) Y
  | repr : ∀ {C : Cat} {X : Obj C} {Y : ReprObj C} (f : HomRepr X Y), Hom X (Repr Y)
  | map : ∀ {C D : Cat} {X Y : Obj C} (F : Func C D) (f : Hom X Y), Hom (App F X) (App F Y)
  | var : ∀ {C : Cat} {X Y : ℕ}, HomVar C X Y → Hom (Var C X) (Var C Y)

/-Provided LAdj is bigger than map, every Hom constructor make homs from homs between smaller objects.
By smaller I mean that -/

end

namespace Hom

def id : ∀ {C : Cat} {X : Obj C}, Hom X X
  | _, Obj.Var C X => Hom.var (HomVar.id _)
  | _, Obj.App F X => Hom.map F Hom.id
  | _, Obj.Repr (ReprObj.Prod X Y) => repr (HomRepr.prod (Hom.projComp Proj.fst Hom.id) (Hom.projComp Proj.snd Hom.id))
  | _, Obj.Repr (ReprObj.RAdj F H Y) => repr (HomRepr.radj F H (Hom.projComp (Proj.counit F H) Hom.id))
  | _, Obj.Repr (ReprObj.Top C) => repr HomRepr.topMk
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
def topMk {C : Cat} {X : Obj C} : Hom X (Top C) :=
  repr HomRepr.topMk

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

def coreprComp : ∀ {C : Cat} {X : CoreprObj C} {Y Z : Obj C}, HomCorepr X Y → Hom Y Z → HomCorepr X Z
  | _, _, _, _, HomCorepr.coprod f g, h => HomCorepr.coprod (comp f h) (comp g h)
  | _, _, _, _, HomCorepr.ladj F H f, g => HomCorepr.ladj _ _ (comp f (Hom.map F g))
  | _, _, _, _, HomCorepr.botMk, _ => HomCorepr.botMk


def compRepr : ∀ {C : Cat} {X Y : Obj C} {Z : ReprObj C}, Hom X Y → HomRepr Y Z → HomRepr X Z
  | _, _, _, _, f, HomRepr.prod g h => HomRepr.prod (comp f g) (comp f h)
  | _, _, _, _, f, HomRepr.radj F H g => HomRepr.radj _ _ (comp (Hom.map F f) g)
  | _, _, _, _, _, HomRepr.topMk => HomRepr.topMk

def comp : ∀ {C : Cat} {X Y Z : Obj C}, Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, _, Hom.corepr f, g => corepr (coreprComp f g)
  | _, _, _, _, f, Hom.repr g => repr (compRepr f g)
  | _, W, Y, Z, Hom.projComp (Y := X) f g, h =>
    have : size X + size Z < size W + size Z :=
      by linarith [size_lt_of_proj f]
    Hom.projComp f (comp g h)
  | _, W, X, Z, f, Hom.compEmb (Y := Y) g h =>
    have : size W + size Y < size W + size Z :=
      by linarith [size_lt_of_emb h]
    compEmb (f.comp g) h
  | _, _, _, _, prod f g, projComp Proj.fst h => comp f h
  | _, W, Obj.Prod X Y, Z, prod f g, projComp Proj.snd h =>
    have : size Y < 1 + size X + size Y := by linarith
    comp g h
  | _, _, _, _, compEmb f Emb.inl, coprod g h => f.comp g
  | _, W, Obj.Coprod X Y, Z, compEmb f Emb.inr, coprod g h =>
    have : size Y < 1 + size X + size Y := by linarith
    f.comp h
  | _, _, _, _, var f, var g => var (HomVar.comp f g)
  | _, _, _, _, map F f, map _ g => map _ (comp f g)
  --| _, App F X, _, _, map _ (projComp _ _), projComp (Proj.counit _ _) _ => sorry  --Leave it
  --   cases f

  -- -- | _, _, _, _, compEmb _ _, map _ _ => sorry
  | _, _, _, _, _, _ => sorry

end
termination_by comp C X Y Z f g => (size X + size Z, size Y, 1)
               coreprComp C X Y Z f g => (size (Corepr X) + size Z, size Y, 0)
               compRepr C X Y Z f g => (size X + size (Repr Z), size Y, 0)

def LAdjSymm {C D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj D} {Y : Obj C}
    (f : Hom (Obj.LAdj F H X) Y) : Hom X (App F Y) :=
  Hom.comp (Hom.compEmb Hom.id (Emb.unit _ H)) (map F f)

def RAdjSymm {C D : Cat} (F : Func C D) (H : HasRAdj F) {X : Obj C} {Y : Obj D}
    (f : Hom X (Obj.RAdj F H Y)) : Hom (App F X) Y :=
  Hom.comp (map F f) (Hom.projComp (Proj.counit _ H) Hom.id)

def ladjMap {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj D} (f : Hom X Y) :
    Hom (LAdj F H X) (LAdj F H Y) :=
  ladj _ _ (comp f (unit _ _))

def radjMap {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj D} (f : Hom X Y) :
    Hom (RAdj F H X) (RAdj F H Y) :=
  radj _ _ (comp (counit _ _) f)

def ladjPreserveBot {C D : Cat} (F : Func C D) (H : HasLAdj F) : Hom (LAdj F H (Obj.Bot _)) (Obj.Bot _) :=
  ladj _ _ botMk

def radjPreserveTop {C D : Cat} (F : Func C D) (H : HasRAdj F) : Hom (Obj.Top _) (RAdj F H (Obj.Top _)) :=
  radj _ _ topMk

def ladjPreserveCoprod {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj D} :
    Hom (LAdj F H (Obj.Coprod X Y)) (Obj.Coprod (LAdj F H X) (LAdj F H Y)) :=
  ladj _ _ (coprod (LAdjSymm _ H inl) (LAdjSymm _ H inr))

def ladjPreserveCoprodSymm {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj D} :
    Hom (Obj.Coprod (LAdj F H X) (LAdj F H Y)) (LAdj F H (Obj.Coprod X Y)) :=
  coprod (ladj _ _ (comp (unit F H) (map F (ladjMap _ _ inl))))
         (ladj _ _ (comp (unit F H) (map F (ladjMap _ _ inr))))

def radjPreserveProd {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj D} :
    Hom (Obj.Prod (RAdj F H X) (RAdj F H Y)) (RAdj F H (Obj.Prod X Y)) :=
  radj _ _ (prod (RAdjSymm _ H fst) (RAdjSymm _ H snd))

def radjPreserveProdSymm {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj D} :
    Hom (RAdj F H (Obj.Prod X Y)) (Obj.Prod (RAdj F H X) (RAdj F H Y)) :=
  prod (radj _ _ (comp (map F (radjMap _ _ fst)) (counit F H)))
       (radj _ _ (comp (map F (radjMap _ _ snd)) (counit F H)))

def preserveBotOfHasRAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) :
    Hom (App F (Obj.Bot _)) (Obj.Bot _):=
  RAdjSymm _ H botMk

def preserveTopOfHasLAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) :
    Hom (Obj.Top _) (App F (Obj.Top _)) :=
  LAdjSymm _ H topMk

def preserveCoprodOfHasRAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj C} :
    Hom (App F (Obj.Coprod X Y)) (Obj.Coprod (App F X) (App F Y)) :=
  RAdjSymm _ H (coprod (radj _ _ inl) (radj _ _ inr))

def preserveCoprodOfHasRAdjSymm {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj C} :
    Hom (Obj.Coprod (App F X) (App F Y)) (App F (Obj.Coprod X Y)) :=
  coprod (map F inl) (map F inr)

def preserveProdOfHasLAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj C} :
    Hom (Obj.Prod (App F X) (App F Y)) (App F (Obj.Prod X Y)) :=
  LAdjSymm _ H (prod (ladj _ _ fst) (ladj _ _ snd))

def preserveProdOfHasLAdjSymm {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj C} :
    Hom (App F (Obj.Prod X Y)) (Obj.Prod (App F X) (App F Y)) :=
  prod (map F fst) (map F snd)

section

def asCorepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C}, Hom (Corepr X) Y → HomCorepr X Y
  | _, _, _, Hom.corepr f => f
  | _, CoreprObj.Bot _, _, _ => HomCorepr.botMk
  | _, CoreprObj.Coprod X Y, _, f => HomCorepr.coprod (comp (ofEmb Emb.inl) f) (comp (ofEmb Emb.inr) f)
  | _, CoreprObj.LAdj F H X, _, f => HomCorepr.ladj _ _ (comp (ofEmb (Emb.unit F H)) (map F f))

def asRepr : ∀ {C : Cat} {X : Obj C} {Y : ReprObj C}, Hom X (Repr Y) → HomRepr X Y
  | _, _, _, Hom.repr f => f
  | _, _, ReprObj.Prod X Y, f => HomRepr.prod (comp f (ofProj Proj.fst)) (comp f (ofProj Proj.snd))
  | _, _, ReprObj.RAdj F H X, f => HomRepr.radj _ _ (comp (map F f) (ofProj (Proj.counit F H)))
  | _, _, ReprObj.Top _, _ => HomRepr.topMk

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
- If it can be written as `f ; corepr g` then it is unless the first rule applies. What if there are two different ways of doing this?,
    Try to make sure `f` is not of that form
    Also `corepr g` should remain a subterm after `f` and `corepr g` are composed and cut eliminated.
- If it can be written as `repr_mk ; f` then it is unless the first rule applies.
- Not sure what else there is, just associativity of `projComp` and `compEmb`
-/

/-
Questions: What is shrinking? I have to make sure that everything splits into smaller homs.
I decided to do products before LAdj. Why? I don't think this applies if I insist on objects shrinking.

-/

open Hom

def getCompCorepr :
    ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y),
      Option (Σ R : CoreprObj C, Hom X (Corepr R) × HomCorepr R Y × Bool)
      --Bool is true if the `Hom X (Corepr R)` is the identity
  | _, Corepr R, _, f => some ⟨_, Hom.id, asCorepr f, true⟩
  | _, _, _, var _ => none
  | _, _, _, topMk => none
  | _, _, _, Hom.repr (HomRepr.radj F H f) => none
  | _, _, _, map F f => none
  | _, _, _, projComp f g =>
    match getCompCorepr g with
    | none => none
    | some ⟨R, g, h, _⟩ => some ⟨R, projComp f g , h, false⟩
  | _, _, _, compEmb f h =>
    match getCompCorepr f with
    | none => none
    | some ⟨R, f, g, _⟩ => some ⟨R, f, coreprComp g (ofEmb h), false⟩
  | _, _, _, Hom.repr (HomRepr.prod f g) =>
    match getCompCorepr f, getCompCorepr g with
    | some ⟨R₁, f₁, f₂, _⟩, some ⟨R₂, g₁, g₂, _⟩ =>
        let nf := normalize f₁
        let ng := normalize g₁
        if hr : R₁ = R₂
          then if (hr ▸ nf) = ng
            then by
              subst R₁
              match R₂, nf, f₂, g₂ with
              | _, nf, HomCorepr.coprod f₂ f₃, HomCorepr.coprod g₂ g₃ =>
                exact some ⟨_, nf, HomCorepr.coprod (prod f₂ g₂) (prod f₃ g₃), false⟩
              | _, nf, HomCorepr.botMk, HomCorepr.botMk => exact some ⟨_, nf, HomCorepr.botMk, false⟩
              | _, nf, HomCorepr.ladj _ _ _, _ => exact none
            else none
        else none
    | _, _ => none

def getReprComp :
    ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Option (Σ R : ReprObj C, HomRepr X R × Hom (Repr R) Y × Bool)
  | _, Corepr R, _, f => none
  | _, _, Obj.Repr R, f => some ⟨_, asRepr f, Hom.id, true⟩
  | _, _, _, var _ => none
  | _, _, _, map F f => none
  | _, _, _, projComp f g =>
    match getReprComp g with
    | none => none
    | some ⟨R, g, h, _⟩ => some ⟨R, compRepr (ofProj f) g, h, false⟩
  | _, _, _, compEmb f h =>
    match getReprComp f with
    | none => none
    | some ⟨R, f, g, _⟩ => some ⟨R, f, compEmb g h, false⟩

def normalizeCorepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C} (f : HomCorepr X Y),
    HomCorepr X Y
  | _, _, _, HomCorepr.coprod f g => HomCorepr.coprod (normalize f) (normalize g)
  | _, _, _, HomCorepr.botMk => HomCorepr.botMk
  | _, _, _, HomCorepr.ladj F H f => HomCorepr.ladj F H (normalize f)

def normalizeRepr : ∀ {C : Cat} {X : Obj C} {Y : ReprObj C} (f : HomRepr X Y),
    HomRepr X Y
  | _, _, _, HomRepr.radj F H f => HomRepr.radj F H (normalize f)
  | _, _, _, HomRepr.prod f g => HomRepr.prod (normalize f) (normalize g)
  | _, _, _, HomRepr.topMk => HomRepr.topMk

def normalize : ∀ {C : Cat} {X Y : Obj C} (f : Hom X Y), Hom X Y := sorry

end

end Hom
