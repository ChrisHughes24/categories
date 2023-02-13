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

mutual

inductive CoreprObj : Cat → Type
  | Coprod {C : Cat} (X Y : PreObj C) : CoreprObj C
  | LAdj {C D : Cat} (F : Func C D) : HasLAdj F → PreObj D → CoreprObj C
  | Bot : (C : Cat) → CoreprObj C

inductive ReprObj : Cat → Type
  | Prod {C : Cat} : PreObj C → PreObj C → ReprObj C
  | RAdj {C D : Cat} (F : Func C D) : HasRAdj F → PreObj D → ReprObj C
  | Top : (C : Cat) → ReprObj C

inductive PreObj : Cat → Type
  | Corepr : ∀ {C : Cat}, CoreprObj C → PreObj C
  | Var : (C : Cat) → ℕ → PreObj C
  | App' : ∀ {C D : Cat}, Func C D → PreObj C → PreObj D
  | Repr : ∀ {C : Cat}, ReprObj C → PreObj C

end

open PreObj

@[match_pattern, simp]
nonrec def PreObj.Coprod {C : Cat} (X Y : PreObj C) : PreObj C :=
  Corepr (CoreprObj.Coprod X Y)

@[match_pattern, simp]
nonrec def PreObj.Prod {C : Cat} (X Y : PreObj C) : PreObj C :=
  PreObj.Repr (ReprObj.Prod X Y)

@[match_pattern, simp]
nonrec def PreObj.LAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) (X : PreObj D) : PreObj C :=
  Corepr (CoreprObj.LAdj F H X)

@[match_pattern, simp]
nonrec def PreObj.RAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) (X : PreObj D) : PreObj C :=
  PreObj.Repr (ReprObj.RAdj F H X)

@[match_pattern]
nonrec def PreObj.Bot (C : Cat) : PreObj C :=
  Corepr (CoreprObj.Bot C)

@[match_pattern]
nonrec def PreObj.Top (C : Cat) : PreObj C :=
  PreObj.Repr (ReprObj.Top C)

@[simp]
def PreObj.App : ∀ {C D : Cat} (F : Func C D) (X : PreObj C), PreObj D
  | _, _, F, Coprod X Y =>
    if hR : HasRAdj F
    then Coprod (App F X) (App F Y)
    else App' F (Coprod X Y)
  | _, _, F, PreObj.Prod X Y =>
    if hL : HasLAdj F
    then Prod (App F X) (App F Y)
    else App' F (PreObj.Prod X Y)
  | _, _, F, PreObj.Bot _ =>
    if hR : HasRAdj F
    then PreObj.Bot _
    else App' F (PreObj.Bot _)
  | _, _, F, PreObj.Top _ =>
    if hL : HasLAdj F
    then PreObj.Top _
    else App' F (PreObj.Top _)
  | _, _, F, X => App' F X

@[simp]
def PreObj.size : ∀ {C : Cat} (X : PreObj C), ℕ
  | _, Corepr (CoreprObj.Coprod X Y) => 1 + max (size X) (size Y)
  | _, Corepr (CoreprObj.LAdj F H X) => 2 + size X
  | _, Corepr (CoreprObj.Bot C) => 1
  | _, Var C n => 1
  | _, App' F X => 1 + size X
  | _, Repr (ReprObj.Prod X Y) => 1 + max (size X) (size Y)
  | _, Repr (ReprObj.RAdj F H X) => 2 + size X
  | _, Repr (ReprObj.Top C) => 1

inductive PreObj.Valid : ∀ {C : Cat} (X : PreObj C), Prop
  | Var : ∀ {C : Cat} (n : ℕ), Valid (Var C n)
  | App : ∀ {C D : Cat} (F : Func C D) (X : PreObj C), Valid X → Valid (App F X)
  | Bot : ∀ {C : Cat}, Valid (Bot C)
  | Top : ∀ {C : Cat}, Valid (Top C)
  | Coprod : ∀ {C : Cat} (X Y : PreObj C), Valid X → Valid Y → Valid (Coprod X Y)
  | Prod : ∀ {C : Cat} (X Y : PreObj C), Valid X → Valid Y → Valid (Prod X Y)
  | LAdj : ∀ {C D : Cat} (F : Func C D) (H : HasLAdj F) (X : PreObj D), Valid X → Valid (LAdj F H X)
  | RAdj : ∀ {C D : Cat} (F : Func C D) (H : HasRAdj F) (X : PreObj D), Valid X → Valid (RAdj F H X)

def Obj (C : Cat) := { X : PreObj C // X.Valid }

namespace Obj

def size {C : Cat} (X : Obj C) : ℕ := PreObj.size X.val

def Var {C : Cat} (n : ℕ) : Obj C := ⟨ PreObj.Var C n, Valid.Var n ⟩

def App {C D : Cat} (F : Func C D) (X : Obj C) : Obj D := ⟨ PreObj.App F X.val, Valid.App F X.val X.2 ⟩

def Coprod {C : Cat} (X Y : Obj C) : Obj C := ⟨ PreObj.Coprod X.val Y.val, Valid.Coprod X.val Y.val X.2 Y.2 ⟩

def Prod {C : Cat} (X Y : Obj C) : Obj C := ⟨ PreObj.Prod X.val Y.val, Valid.Prod X.val Y.val X.2 Y.2 ⟩

def Bot {C : Cat} : Obj C := ⟨ PreObj.Bot C, Valid.Bot ⟩

def Top {C : Cat} : Obj C := ⟨ PreObj.Top C, Valid.Top ⟩

def LAdj {C D : Cat} (F : Func C D) (H : HasLAdj F) (X : Obj D) : Obj C :=
  ⟨ PreObj.LAdj F H X.val, Valid.LAdj F H X.val X.2 ⟩

def RAdj {C D : Cat} (F : Func C D) (H : HasRAdj F) (X : Obj D) : Obj C :=
  ⟨ PreObj.RAdj F H X.val, Valid.RAdj F H X.val X.2 ⟩

theorem size_app : ∀ {C D : Cat} (F : Func C D) (X : Obj C), size (App F X) ≤ 1 + size X := sorry

end Obj

inductive HomVar (C : Cat) : (X Y : ℕ) → Type
  | id : ∀ (X : ℕ), HomVar C X X
  | varComp {X Y Z : ℕ} (n : ℕ) (f : HomVar C Y Z) : HomVar C X Z
  deriving DecidableEq

def HomVar.comp {C : Cat} : ∀ {X Y Z : ℕ} (f : HomVar C X Y) (g : HomVar C Y Z), HomVar C X Z
  | _, _, _, HomVar.id _, f => f
  | _, _, _, HomVar.varComp n f, g => HomVar.varComp n (HomVar.comp f g)

open PreObj

mutual

/- Currently have no way of writing certain homs.
-- map F (LAdj _ _ _) ; counit : App F (LAdj G _ _) -> App F (Radj F _ _)
-- map F (projComp (fst or snd)) ; counit : App F (X × _) -> App F (Radj F _ X) -/

inductive ProdProj : ∀ {C : Cat}, PreObj C → PreObj C → PreObj C → Type
  | fst : ∀ {X Y : PreObj C}, ProdProj X Y X
  | snd : ∀ {X Y : PreObj C}, ProdProj X Y Y

inductive CompCounit : ∀ {C D : Cat}, PreObj D → PreObj C → Type
  | counit : ∀ {C D : Cat} (F : Func D C) (H : HasRAdj F) (X : PreObj C),
      CompCounit (RAdj F H X) X
  | mapLAdjCompCounit : ∀ {C D E : Cat} (F : Func C D) (G : Func C E) (HF : HasLAdj F) (HG : HasRAdj G)
      {X : PreObj D} {Y : PreObj E} (f : PreHom X (App F (RAdj G HG Y))), CompCounit (LAdj F HF X) Y
  | mapProjComp : ∀ {C : Cat} {W X Y Z : PreObj C} (f : ProdProj W X Y) (g : CompCounit Y Z),
      CompCounit (Prod X Y) Z

inductive Proj : ∀ {C : Cat}, PreObj C → PreObj C → Type
  | prodProj : ∀ {X Y Z : PreObj C}, ProdProj X Y Z → Proj (Prod X Y) Z
  | compCounit : ∀ {C D : Cat} (F : Func D C) (H : HasRAdj F) {X : PreObj D} {Y : PreObj C}
      (f : CompCounit X Y), Proj (App' F X) Y

inductive HomCorepr : {C : Cat} → CoreprObj C → PreObj C → Type
  | coprod {C : Cat} {X Y Z : PreObj C} (f : PreHom X Z) (g : PreHom Y Z) : HomCorepr (CoreprObj.Coprod X Y) Z
  | ladj {C D : Cat} (F : Func C D) (H : HasLAdj F) {X : PreObj D} {Y : PreObj C}
      (f : PreHom X (App F Y)) : HomCorepr (CoreprObj.LAdj F H X) Y
  | botMk {C : Cat} {X : PreObj C} : HomCorepr (CoreprObj.Bot C) X

inductive CoprodEmb : ∀ {C : Cat}, PreObj C → PreObj C → PreObj C → Type
  | inl : ∀ {X Y : PreObj C}, CoprodEmb X X Y
  | inr : ∀ {X Y : PreObj C}, CoprodEmb Y X Y

inductive UnitComp : ∀ {C D : Cat}, PreObj C → PreObj D → Type
  | unit : ∀ {C D : Cat} (F : Func D C) (H : HasLAdj F) (X : PreObj C),
      UnitComp X (LAdj F H X)
  | unitCompMapRAdj : ∀ {C D E : Cat} (F : Func C D) (G : Func C E) (HF : HasRAdj F) (HG : HasLAdj G)
      {X : PreObj E} {Y : PreObj D} (f : PreHom (App F (LAdj G HG X)) Y), UnitComp X (RAdj F HF Y)
  | compMapEmb : ∀ {C : Cat} {W X Y Z : PreObj C} (f : UnitComp W X) (g : CoprodEmb X Y Z),
      UnitComp W (Coprod Y Z)

inductive Emb : ∀ {C : Cat}, PreObj C → PreObj C → Type
  | coprodEmb : ∀ {X Y Z : PreObj C}, CoprodEmb X Y Z → Emb X (Coprod Y Z)
  | unitComp : ∀ {C D : Cat} (F : Func D C) (H : HasLAdj F) {X : PreObj C} {Y : PreObj D}
      (f : UnitComp X Y), Emb X (App' F Y)

inductive HomRepr : {C : Cat} → PreObj C → ReprObj C → Type
  | prod {C : Cat} {X : PreObj C} {Y Z : PreObj C}
    (f : PreHom X Y) (g : PreHom X Z) : HomRepr X (ReprObj.Prod Y Z)
  | radj {C D : Cat} (F : Func C D) (H : HasRAdj F) {X : PreObj C} {Y : PreObj D}
    (f : PreHom (App F X) Y) : HomRepr X (ReprObj.RAdj F H Y)
  | topMk {C : Cat} {X : PreObj C} : HomRepr X (ReprObj.Top C)

inductive PreHom : ∀ {C : Cat}, PreObj C → PreObj C → Type
  | projComp : ∀ {C : Cat} {X Y Z : PreObj C} (f : Proj X Y) (g : PreHom Y Z), PreHom X Z
  | compEmb : ∀ {C : Cat} {X : PreObj C} {Y Z : PreObj C} (f : PreHom X Y) (g : Emb Y Z), PreHom X Z
  | corepr : ∀ {C : Cat} {X : CoreprObj C} {Y : PreObj C} (f : HomCorepr X Y), PreHom (Corepr X) Y
  | repr : ∀ {C : Cat} {X : PreObj C} {Y : ReprObj C} (f : HomRepr X Y), PreHom X (Repr Y)
  | map' : ∀ {C D : Cat} {X Y : PreObj C} (F : Func C D) (f : PreHom X Y), PreHom (App' F X) (App' F Y)
  | var : ∀ {C : Cat} {X Y : ℕ}, HomVar C X Y → PreHom (Var C X) (Var C Y)

/- Provided LAdj is bigger than map, every Hom constructor make homs from homs between smaller objects.
By smaller I mean that -/

end

def Proj.fst {C : Cat} {X Y : PreObj C} : Proj (Prod X Y) X :=
  prodProj ProdProj.fst

def Proj.snd {C : Cat} {X Y : PreObj C} : Proj (Prod X Y) Y :=
  prodProj ProdProj.snd

def Proj.counit {C : Cat} {D : Cat} (F : Func D C) (H : HasRAdj F) {X : PreObj C} :
    Proj (App' F (RAdj F H X)) X :=
  compCounit F H (CompCounit.counit F H X)

def Emb.inl {C : Cat} {X Y : PreObj C} : Emb X (Coprod X Y) :=
  coprodEmb CoprodEmb.inl

def Emb.inr {C : Cat} {X Y : PreObj C} : Emb Y (Coprod X Y) :=
  coprodEmb CoprodEmb.inr

def Emb.unit {C : Cat} {D : Cat} (F : Func D C) (H : HasLAdj F) {X : PreObj C} :
    Emb X (App' F (LAdj F H X)) :=
  unitComp F H (UnitComp.unit F H X)

theorem size_lt_of_emb {C : Cat} {X Y : PreObj C} (f : Emb X Y) : PreObj.size X < PreObj.size Y := sorry

theorem size_lt_of_proj {C : Cat} {X Y : PreObj C} (f : Proj X Y) : PreObj.size Y < PreObj.size X := sorry

def Hom {C : Cat} (X Y : Obj C) : Type :=
  PreHom X.1 Y.1

namespace PreHom

def id : ∀ {C : Cat} {X : PreObj C}, PreHom X X
  | _, PreObj.Var C X => PreHom.var (HomVar.id _)
  | _, PreObj.App' F X => PreHom.map' F PreHom.id
  | _, PreObj.Repr (ReprObj.Prod X Y) => repr (HomRepr.prod (PreHom.projComp Proj.fst PreHom.id) (PreHom.projComp Proj.snd PreHom.id))
  | _, PreObj.Repr (ReprObj.RAdj F H Y) => repr (HomRepr.radj F H (PreHom.projComp (Proj.counit F H) PreHom.id))
  | _, PreObj.Repr (ReprObj.Top C) => repr HomRepr.topMk
  | _, PreObj.Corepr (CoreprObj.Coprod X Y) => corepr (HomCorepr.coprod (Hom.compEmb Hom.id Emb.inl) (Hom.compEmb Hom.id Emb.inr))
  | _, PreObj.Corepr (CoreprObj.LAdj F H X) => corepr (HomCorepr.ladj F H (Hom.compEmb Hom.id (Emb.unit F H)))
  | _, PreObj.Corepr (CoreprObj.Bot C) => corepr HomCorepr.botMk

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
  | _, _, _, _, map' F f, map' _ g => map' _ (comp f g)
  | _, _, _, _, map' _ (projComp _ _), projComp (Proj.counit _ _) _ => sorry  --New constructor
  | _, _, _, _, map' _ (Hom.repr (HomRepr.radj _ _ f)), projComp (Proj.counit _ _) g => f.comp g
  | _, _, _, _, map' _ (Hom.corepr HomCorepr.botMk), projComp (Proj.counit _ _) _ => sorry --Things must preserve coproducts in a stronger way.
  | _, _, _, _, map' G (Hom.corepr (HomCorepr.ladj F H f)), projComp (Proj.counit _ _) g => sorry --New constructor
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

def normalize {C : Cat} {X Y : Obj C} (f : Hom X Y) : Hom X Y :=
  match getCompCorepr f with
  | none =>
    match getReprComp f with
    | none =>

end

end Hom
