import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
/-!
# Categories

This file contains a level polymorphic definition of categories,
based on the definition in mathlib's CategoryTheory library.

## Universe levels

Following mathlib's convention, we use two universe levels:
- `u` for the objects
- `v` for the morphisms

-/

universe v u

namespace Cat

/-!
### Quiver

A quiver is a directed graph, providing the basic structure of objects and morphisms.
-/

/-- A quiver is just a type with a Hom relation between objects -/
class Quiver (obj : Type u) : Type max u v where
  /-- The type of morphisms from one object to another -/
  Hom : obj → obj → Sort v

class FiniteQuiver (obj : Type u) extends Quiver.{v} obj where
  finite_objects : Finite obj
  finite_morphisms : ∀ (v w : obj), Finite (Hom v w)

open Cat.Quiver

/-- Notation for morphisms between objects -/
infixr:50 " ⇒ " => Hom

/-!
### Deductive System

A Deductive system is a quiver with identity morphisms and composition.
-/

class DeductiveSystem (obj : Type u) : Type max u v extends Quiver.{v} obj where
  /-- The identity morphism on an object -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g` -/
  comp : ∀ {X Y Z : obj}, (Hom X Y) → (Hom Y Z) → (Hom X Z)

/-- Notation for the identity morphism in a category -/
notation "𝟙" => DeductiveSystem.id

/-- Notation for composition of morphisms in a category (diagrammatic order) -/
infixr:80 " ≫ " => DeductiveSystem.comp

/-!
### Category

A category is a Deductive structure satisfying three axioms:
identity laws and associativity.
-/

/--
The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need
 to be specified explicitly, as `Category.{v} C`.
-/
class Category (obj : Type u) : Type max u v extends DeductiveSystem.{v} obj where
  /-- left identity for composition -/
  id_comp : ∀ {X Y : obj} (f : Hom X Y), 𝟙 X ≫ f = f
  /-- right identity for composition -/
  comp_id : ∀ {X Y : obj} (f : Hom X Y), f ≫ 𝟙 Y = f
  /-- Composition is associative -/
  assoc : ∀ {W X Y Z : obj} (f : W ⇒ X) (g : X ⇒ Y) (h : Y ⇒ Z),
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

class FiniteCategory (obj : Type u) extends Category.{v} obj, FiniteQuiver.{v} obj

attribute [simp] Category.id_comp
attribute [simp] Category.comp_id
attribute [simp] Category.assoc

/-!
### Common category sizes
-/

/-- A small category is one where objects and morphisms live in the same universe -/
abbrev SmallCategory (obj : Type u) := Category.{u} obj

/-- A large category is one where objects live one universe level above morphisms -/
abbrev LargeCategory (obj : Type (u + 1)) := Category.{u} obj

/-!
### Examples
-/

/--
Set: The category of types and functions (analogous to the category Set bounded by a
universe size)
-/
instance : Quiver (Type u) where
  Hom x y := x -> y

instance : DeductiveSystem (Type u) where
  id _X x := x
  comp f g := fun x => g (f x)

instance : Category (Type u) where
  id_comp := by
    intro X Y f
    rfl

  comp_id := by
    intro X Y f
    rfl

  assoc := by
    intro X Y Z W f g h
    rfl

/--
Set: The category of types and functions (analogous to the category Set bounded by a
universe size)
-/
structure Rel : Type (u + 1) where
  obj : Type u

instance : Quiver Rel.{u} where
  Hom x y := x.obj -> y.obj -> Prop

instance RelDeductiveSystem : DeductiveSystem Rel.{u} where
  id _X x y := x = y
  comp f g x z := ∃ y , f x y ∧ g y z

theorem rel_assoc {X Y : Type u}
  (f : W → X → Prop)(g : X → Y → Prop)(h : Y → Z → Prop)
  (w : W) (z : Z) :
  (∃ (y' : Y), (∃ (x' : X), f w x' ∧ g x' y') ∧ h y' z) ↔ ∃ (x' : X), f w x' ∧ ∃ (y' : Y), g x' y' ∧ h y' z := by
  constructor
  · intro lhs
    rcases lhs with ⟨y' , ⟨inner, hyz⟩⟩
    rcases inner with ⟨x', fwx_gxy⟩
    refine ⟨x', ?_⟩
    · constructor
      · apply And.left
        exact fwx_gxy
      · refine ⟨y', ?_⟩
        constructor
        · apply And.right
          exact fwx_gxy
        · exact hyz
  · intro rhs
    rcases rhs with ⟨x' , ⟨fwx, inner⟩⟩
    rcases inner with ⟨y', gxy_hyz⟩
    refine ⟨y', ?_⟩
    · constructor
      · refine ⟨x', ?_⟩
        constructor
        · exact fwx
        · apply And.left
          exact gxy_hyz
      · apply And.right
        exact gxy_hyz

instance RelCategory : Category (Rel.{u}) where
  id_comp := by
    intro X Y f
    simp [DeductiveSystem.comp]
    apply funext
    intro x
    apply funext
    intro y
    simp [DeductiveSystem.id]

  comp_id := by
    intro X Y f
    simp [DeductiveSystem.comp]
    apply funext
    intro x
    apply funext
    intro y
    simp [DeductiveSystem.id]

  assoc := by
    intro W X Y Z f g h
    simp [DeductiveSystem.comp]
    apply funext
    intro w
    apply funext
    intro z
    simp
    apply rel_assoc f g h w z

/--
Structured sets (Monoids): Any algebraic theory forms a category with:
  · Obj: Algebraic objects
  · Mor: homomorphisms

We show this in the case of the category of monoids
-/

structure Mon where
  (α : Type u)
  str: Monoid α

instance (M : Mon) : Monoid M.α := M.str

instance : Quiver Mon where
  Hom M N := MonoidHom M.α N.α


-- In order to show that Mon is a DeductiveSystem, we need to show
-- the identity is a monoid hom and the composition of two monoid homs
-- is a monoid hom
def id_hom (M : Type u) [Monoid M] : MonoidHom M M := by
  refine {toFun := ?_, map_one' := ?_, map_mul' := ?_}
  · exact id
  · simp
  · simp

def comp_hom {M N P : Type u} [Monoid M][Monoid N][Monoid P]
  (f : MonoidHom M N)(g : MonoidHom N P) : MonoidHom M P  := by
  refine {toFun := ?_, map_one' := ?_, map_mul' := ?_}
  · intro m
    apply g.toFun
    apply f.toFun
    exact m
  · simp
  · simp

instance : DeductiveSystem Mon where
  id M := by
    simp [Quiver.Hom]
    apply id_hom

  comp := comp_hom

instance : Category Mon where
  id_comp := by
    intro M N f
    simp [DeductiveSystem.comp, comp_hom]
    apply MonoidHom.ext
    intro m
    simp [DeductiveSystem.id, id_hom]

  comp_id := by
    intro M N f
    simp [DeductiveSystem.comp, comp_hom]
    apply MonoidHom.ext
    intro m
    simp [DeductiveSystem.id, id_hom]

  assoc := by
    intro M N P f g h
    simp [DeductiveSystem.comp, comp_hom]

/--
Monoids: Given a monoid M, we have an associated one object category which we denote by
B M (the 'delooping' of M)
-/

structure B (M : Type u) : Type u

instance (M : Type u) [Monoid M] : Quiver (B M) where
  Hom _X _Y := M

instance (M : Type u) [Monoid M] : DeductiveSystem (B M) where
  id _X := 1
  comp m n := m * n

instance (M : Type u) [Monoid M] : Category (B M) where
  id_comp := by
    intro X Y m
    simp [DeductiveSystem.id, DeductiveSystem.comp]

  comp_id := by
    intro X Y m
    simp [DeductiveSystem.id, DeductiveSystem.comp]

  assoc := by
    intro _X _Y _Z _W m n p
    exact mul_assoc m n p

/--
Preorder: Given a preorder P, we have an associated category with objects the same
as P and a morphism from p to q if p ≤ q
-/

structure Pre (P : Type u) : Type u where
  el : P

instance (P : Type u) [Preorder P] : Quiver (Pre P) where
  Hom p q := p.el ≤ q.el

instance (P : Type u) [Preorder P] : DeductiveSystem (Pre P) where
  id p := by
    simp [Quiver.Hom]

  comp e1 e2 := by
    simp [Quiver.Hom]
    apply le_trans e1 e2

/--
As a preorder has at most one morphism between any two objects
all equations are automatically satisfied
-/
instance (P : Type u) [Preorder P] : Category (Pre P) where
  id_comp := by
    intros p q p_le_q
    rfl

  comp_id := by
    intros p q p_le_q
    rfl

  assoc := by
    intros p q r s pq qr rs
    rfl

/--
Discrete Cat: Given a Set (really type) X, we have an associated discrete category
with only identity homs

Note: For the hom types we use the equality type which may have many distinct proofs
that x = x depending on the ambient type theory
-/
structure Disc(X : Type u) : Type u where
  el : X

instance (X : Type u) [Finite X] : Finite (Disc X) :=
  Finite.of_equiv X ⟨Disc.mk, Disc.el, fun _ => rfl, fun _ => rfl⟩

instance (X : Type u) : Quiver (Disc X) where
  Hom p q := p = q

instance (X : Type u) [Finite X] : FiniteQuiver (Disc X) where
  finite_objects := inferInstance
  finite_morphisms v w := by
    show Finite (v = w)
    infer_instance

instance (X : Type u) : DeductiveSystem (Disc X) where
  id X := by
    rfl

  comp e1 e2 := by
    rw [e1, e2]
    rfl

instance (X : Type u) : Category (Disc X) where
  id_comp := by
    intros p q eq
    rfl

  comp_id := by
    intros p q eq
    rfl

  assoc := by
    intros p q r s e1 e2 e3
    rfl

instance {n : ℕ} : Quiver (Fin n) where
  Hom n m := n ≤ m

instance {n : ℕ} : DeductiveSystem (Fin n) where
  id _ := Nat.le_refl _
  comp h₁ h₂ := Nat.le_trans h₁ h₂

instance {n : ℕ} : Category (Fin n) where
  id_comp _r := by rfl
  comp_id _r := by rfl
  assoc _f _g _h := by rfl

end Cat
