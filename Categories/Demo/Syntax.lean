
set_option linter.unusedVariables false

class PreCatSystem (Cat : Type) :=
  [ decEq : DecidableEq Cat ]
  ( Func : Cat → Cat → Type )
  ( HasLAdj : ∀ {C D : Cat}, Func C D → Prop )
  [ decidableLAdj : ∀ (C D : Cat) (F : Func C D), Decidable (HasLAdj F) ]
  ( HasRAdj : ∀ {C D : Cat}, Func C D → Prop )
  [ decidableRAdj : ∀ (C D : Cat) (F : Func C D), Decidable (HasRAdj F) ]

/- We have a system of Categories -/
variable {Cat : Type} [PreCatSystem Cat]

attribute [instance] PreCatSystem.decEq PreCatSystem.decidableLAdj PreCatSystem.decidableRAdj

open PreCatSystem

inductive Obj : Cat → Type
  | Var : (C : Cat) → ℕ → Obj C
  | App : ∀ {C D : Cat}, Func C D → Obj C → Obj D
  | Prod {C : Cat} : Obj C → Obj C → Obj C
  | RAdj {C D : Cat} (F : Func C D) : HasRAdj F → Obj D → Obj C
  | Top : (C : Cat) → Obj C
  | Coprod {C : Cat} (X Y : Obj C) : Obj C
  | LAdj {C D : Cat} (F : Func C D) : HasLAdj F → Obj D → Obj C
  | Bot : (C : Cat) → Obj C

open Obj

inductive Hom : ∀ {C D : Cat}, Obj C → Obj D → Type
  | var : ∀ {C : Cat} (X Y : ℕ) (n : ℕ), Hom (Var C X) (Var C Y)
  | map : ∀ {C D : Cat} (F : Func C D) {X Y : Obj C}, Hom X Y → Hom (App F X) (App F Y)
  | id : ∀ {C : Cat} (X : Obj C), Hom X X
  | comp : ∀ {C : Cat} {X Y Z : Obj C} (f : Hom X Y) (g : Hom Y Z), Hom X Z
  | top : ∀ {C : Cat} (X : Obj C), Hom X (Obj.Top C)
  | bot : ∀ {C : Cat} (X : Obj C), Hom (Obj.Bot C) X
  | coprod : ∀ {C : Cat} {X Y Z : Obj C} (f : Hom X Z) (g : Hom Y Z), Hom (Obj.Coprod X Y) Z
  | inl : ∀ {C : Cat} {X Y : Obj C}, Hom X (Obj.Coprod X Y)
  | inr : ∀ {C : Cat} {X Y : Obj C}, Hom Y (Obj.Coprod X Y)
  | prod : ∀ {C : Cat} {X Y Z : Obj C} (f : Hom X Y) (g : Hom X Z), Hom X (Obj.Prod Y Z)
  | fst : ∀ {C : Cat} {X Y : Obj C}, Hom (Obj.Prod X Y) X
  | snd : ∀ {C : Cat} {X Y : Obj C}, Hom (Obj.Prod X Y) Y
  | radj : ∀ {C D : Cat} (F : Func C D) (H : HasRAdj F) {X : Obj C} {Y : Obj D},
      Hom (App F X) Y → Hom X (Obj.RAdj F H Y)
  | counit : ∀ {C D : Cat} (F : Func C D) (H : HasRAdj F) {X : Obj D},
      Hom (App F (Obj.RAdj F H X)) X
  | radjMap : ∀ {C D : Cat} (F : Func C D) (H : HasRAdj F) {X Y : Obj D} (f : Hom X Y),
      Hom (Obj.RAdj F H X) (Obj.RAdj F H Y)
  | ladj : ∀ {C D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj D} {Y : Obj C},
      Hom X (App F Y) → Hom (Obj.LAdj F H X) Y
  | unit : ∀ {C D : Cat} (F : Func C D) (H : HasLAdj F) {X : Obj D},
      Hom X (App F (Obj.LAdj F H X))
  | ladjMap : ∀ {C D : Cat} (F : Func C D) (H : HasLAdj F) {X Y : Obj D} (f : Hom X Y),
      Hom (Obj.LAdj F H X) (Obj.LAdj F H Y)


