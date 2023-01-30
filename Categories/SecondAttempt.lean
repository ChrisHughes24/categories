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

inductive NotCoreprObj : Cat → Type
  | var : (C : Cat) → ℕ → NotCoreprObj C
  /- Below constructor should never be applied to product when `C ⥤ D` has a LAdj or
  to coproduct when `C ⥤ D` has a RAdj. -/
  | app : ∀ (C D : Cat), Func C D → Obj C → NotCoreprObj D
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

nonrec def Obj.app (C D : Cat) (F : Func C D) (X : Obj C) : Obj D :=
  notCorepr (NotCoreprObj.app C D F X)

nonrec def Obj.coprod {C : Cat} (X Y : Obj C) : Obj C :=
  corepr (CoreprObj.coprod X Y)

nonrec def Obj.prod {C : Cat} (X Y : Obj C) : Obj C :=
  notCorepr (NotCoreprObj.repr C (ReprObj.prod X Y))

nonrec def Obj.LAdj (C D : Cat) (F : Func C D) (H : HasLAdj C D F) (X : Obj D) : Obj C :=
  corepr (CoreprObj.LAdj C D F H X)

nonrec def Obj.RAdj (C D : Cat) (F : Func C D) (H : HasRAdj C D F) (X : Obj D) : Obj C :=
  notCorepr (NotCoreprObj.repr C (ReprObj.RAdj C D F H X))

nonrec def Obj.bot (C : Cat) : Obj C :=
  corepr (CoreprObj.bot C)

nonrec def Obj.top (C : Cat) : Obj C :=
  notCorepr (NotCoreprObj.top C)

nonrec def Obj.repr {C : Cat} (X : ReprObj C) : Obj C :=
  notCorepr (NotCoreprObj.repr C X)

nonrec def Obj.var (C : Cat) (n : ℕ) : Obj C :=
  notCorepr (NotCoreprObj.var C n)

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

inductive HomRepr : ∀ {C : Cat}, NotCoreprObj C → ReprObj C → Type
  /-- Never to be used when `f` and `g` are of the form `f = f₁ ; f₂`, `g = g₁ ; g₂` and
  `f₁ = g₁` -/
  | prod {C : Cat} {X : NotCoreprObj C} {Y Z : Obj C}
    (f : Hom (notCorepr X) Y) (g : Hom (notCorepr X) Z) : HomRepr X (ReprObj.prod Y Z)
  /-- Never to be used when `f` is a composition. -/
  | radj {C D : Cat} (F : Func C D) (H : HasRAdj C D F) {X : NotCoreprObj C} {Y : Obj D}
    (f : Hom (app C D F (notCorepr X)) Y) : HomRepr X (ReprObj.RAdj C D F H Y)

inductive Hom : {C : Cat} → Obj C → Obj C → Type
  | projComp : ∀ {C : Cat} {X Y Z : Obj C} (f : Proj X Y) (g : Hom Y Z), Hom X Z
  | CompEmb : ∀ {C : Cat} {X : NotCoreprObj C} {Y Z : Obj C}
      (f : Hom (notCorepr X) Y) (g : Emb Y Z), Hom (notCorepr X) Z
  | var : ∀ {C : Cat} {X Y : ℕ} (n : ℕ), Hom (var C X) (var C Y)
  | id : ∀ {C : Cat} (X : Obj C), Hom X X
  | top_mk : ∀ {C : Cat} {X : Obj C}, Hom X (top C)
  | map : ∀ {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj C}
      (f : Hom X Y), Hom (app C D F X) (app C D F Y)
  | corepr : ∀ {C : Cat} {X : CoreprObj C} {Y : Obj C} (f : HomCorepr X Y), Hom (corepr X) Y
  | repr : ∀ {C : Cat} {X : NotCoreprObj C} {Y : ReprObj C} (f : HomRepr X Y),
      Hom (notCorepr X) (repr Y)

end

/-- Function checks if `f` and `g` are of the form `f = f₁ ; f₂`, `g = g₁ ; g₂` and
  `f₁ = g₁`  -/
def leftEq : ∀ {C : Cat}, {X Y : Obj C} → Hom X Y → Hom X Y → Option (Σ Z : Obj C, Hom X Z × Hom Z Y × Hom Z Y)
| _, _, _, Hom.projComp f₁ g₁, Hom.projComp f₂ g₂ => _

mutual

def coreprComp : ∀ {C : Cat} {X : CoreprObj C} {Y Z : Obj C}, HomCorepr X Y → Hom Y Z → HomCorepr X Z
  | _, _, _, _, HomCorepr.coprod f g, h => HomCorepr.coprod (comp f h) (comp g h)
  | _, _, _, _, HomCorepr.ladj F H f, g => HomCorepr.ladj _ _ (comp f (Hom.map F g))
  | _, _, _, _, HomCorepr.bot, _ => HomCorepr.bot

def compRepr : ∀ {C : Cat} {X Y : NotCoreprObj C} {Z : ReprObj C}, Hom (notCorepr X) (notCorepr Y) → HomRepr Y Z → HomRepr X Z
  | _, _, _, _, f, HomRepr.prod g h => HomRepr.prod (comp f h) (comp g i)
  | _, _, _, _, HomRepr.radj F H f, HomRepr.radj G K g =>
    HomRepr.radj _ _ (comp (Hom.map F f) (Hom.map G g))

def comp : ∀ {C : Cat} {X Y Z : Obj C}, Hom X Y → Hom Y Z → Hom X Z := sorry

end