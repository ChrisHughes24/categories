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

mutual

inductive HomCorepr : {C : Cat} → CoreprObj C → Obj C → Type
  | coprod {C : Cat} {X Y Z : Obj C} (f : Hom X Z) (g : Hom Y Z) : HomCorepr (CoreprObj.coprod X Y) Z
  | LAdj {C D : Cat} (h : C ≤ D) (H : HasLAdj C D h) {X : Obj D} {Y : Obj C}
      (f : Hom X (app C D h Y)) : HomCorepr (CoreprObj.LAdj C D h H X) Y
  | bot {C : Cat} {X : Obj C} : HomCorepr (CoreprObj.bot C) X

inductive HomRepr : ∀ {C : Cat}, NotCoreprObj C → ReprObj C → Type

inductive Hom : {C : Cat} → Obj C → Obj C → Type

end
