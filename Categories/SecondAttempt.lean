import Mathlib.Init.Algebra.Order

class CatSystem (Cat : Type) extends Preorder Cat :=
  ( HasLAdj : ∀ (C D : Cat), C ≤ D → Prop )
  ( HasRAdj : ∀ (C D : Cat), C ≤ D → Prop )

/- We have a system of Categories and for now we assume that all the functors between
them commute. -/
variable {Cat : Type} [CatSystem Cat]

open CatSystem

--TODO : think about how adjoint preserve products.

mutual

inductive CoreprObj : Cat → Type
  | coprod {C : Cat} (X Y : Obj C) : CoreprObj C
  | LAdj (C D : Cat) (h : C ≤ D) : HasLAdj C D h → Obj D → CoreprObj C
  | bot : (C : Cat) → CoreprObj C

inductive ReprObj : Cat → Type
  | prod {C : Cat} : Obj C → Obj C → ReprObj C
  | RAdj (C D : Cat) (h : C ≤ D) : HasRAdj C D h → Obj D → ReprObj C

inductive NotCoreprObj : Cat → Type
  | var : (C : Cat) → ℕ → NotCoreprObj C
  /- Below constructor should never be applied to product when `C ⥤ D` has a LAdj or
  to coproduct when `C ⥤ D` has a RAdj. -/
  | app : ∀ (C D : Cat), C ≤ D → Obj C → NotCoreprObj D
  | repr : ∀ (C : Cat), ReprObj C → NotCoreprObj C
  | top : (C : Cat) → NotCoreprObj C

inductive Obj : Cat → Type
  | corepr : ∀ {C : Cat}, CoreprObj C → Obj C
  | notCorepr : ∀ {C : Cat}, NotCoreprObj C → Obj C

end

/- Normal form inspired by rewriting procedure in appendix A of http://www.tac.mta.ca/tac/volumes/8/n5/n5.pdf
The exception to the rule being that the normal form of a map into `top` is always `top_mk` unless the
map is from `bot`. -/

open Obj

nonrec def Obj.app (C D : Cat) (h : C ≤ D) (X : Obj C) : Obj D :=
  notCorepr (NotCoreprObj.app C D h X)

nonrec def Obj.coprod {C : Cat} (X Y : Obj C) : Obj C :=
  corepr (CoreprObj.coprod X Y)

nonrec def Obj.prod {C : Cat} (X Y : Obj C) : Obj C :=
  notCorepr (NotCoreprObj.repr C (ReprObj.prod X Y))

nonrec def Obj.LAdj (C D : Cat) (h : C ≤ D) (H : HasLAdj C D h) (X : Obj D) : Obj C :=
  corepr (CoreprObj.LAdj C D h H X)

nonrec def Obj.RAdj (C D : Cat) (h : C ≤ D) (H : HasRAdj C D h) (X : Obj D) : Obj C :=
  notCorepr (NotCoreprObj.repr C (ReprObj.RAdj C D h H X))

nonrec def Obj.bot (C : Cat) : Obj C :=
  corepr (CoreprObj.bot C)

inductive Emb {C : Cat} : Obj C → Obj C → Type
| inl : ∀ {X Y : Obj C}, Emb X (coprod X Y)
| inr : ∀ {X Y : Obj C}, Emb Y (coprod X Y)
| unit : ∀ {D : Cat} (h : D ≤ C) (H : HasLAdj D C h) {X : Obj C},
    Emb X (app D C h (LAdj D C h H X))

inductive Proj {C : Cat} : Obj C → Obj C → Type
| fst : ∀ {X Y : Obj C}, Proj (prod X Y) X
| snd : ∀ {X Y : Obj C}, Proj (prod X Y) Y
| counit : ∀ {D : Cat} (h : D ≤ C) (H : HasRAdj D C h) {X : Obj C},
    Proj (app D C h (RAdj D C h H X)) X

mutual

inductive HomCorepr : {C : Cat} → CoreprObj C → Obj C → Type
  | coprod {C : Cat} {X Y Z : Obj C} (f : Hom X Z) (g : Hom Y Z) : HomCorepr (CoreprObj.coprod X Y) Z
  | ladj {C D : Cat} (h : C ≤ D) (H : HasLAdj C D h) {X : Obj D} {Y : Obj C}
      (f : Hom X (app C D h Y)) : HomCorepr (CoreprObj.LAdj C D h H X) Y
  | bot {C : Cat} {X : Obj C} : HomCorepr (CoreprObj.bot C) X

inductive HomRepr : ∀ {C : Cat}, NotCoreprObj C → ReprObj C → Type
  /-- Never to be used when `f` and `g` are of the form `f = f₁ ; f₂`, `g = g₁ ; g₂` and
  `f₁ = g₁` -/
  | prod {C : Cat} {X : NotCoreprObj C} {Y Z : Obj C}
    (f : Hom (notCorepr X) Y) (g : Hom (notCorepr X) Z) : HomRepr X (ReprObj.prod Y Z)
  /-- Never to be used when `f` is a composition. -/
  | radj {C D : Cat} (h : C ≤ D) (H : HasRAdj C D h) {X : NotCoreprObj C} {Y : Obj D}
    (f : Hom (app C D h (notCorepr X)) Y) : HomRepr X (ReprObj.RAdj C D h H Y)

inductive Hom : {C : Cat} → Obj C → Obj C → Type

end
