/-
Formalization of Category Theory following Awodey's book
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
/-!
# Categories

This file contains a level polymorphic definition of categories,
based on the definition in mathlib's CategoryTheory library.

The definitions are inlined here (not imported) so that theorems and
results can be proven as exercises.

## Universe levels

Following mathlib's convention, we use two universe levels:
- `u` for the objects
- `v` for the morphisms

This allows for flexibility in modeling categories of different sizes.
-/

universe v u

namespace Cat



/-!
### Quiver

A quiver is a directed graph, providing the basic structure of objects and morphisms.
-/

/-- A quiver is just a type with a Hom relation between objects -/
class Quiver (obj : Type u) : Type max u (v + 1) where
  /-- The type of morphisms from one object to another -/
  Hom : obj → obj → Type v

/-- Notation for morphisms between objects -/
infixr:10 " ⟶ " => Quiver.Hom

/-!
### Deductive System

A Deductive system is a quiver with identity morphisms and composition.
-/

class DeductiveSystem (obj : Type u) : Type max u (v + 1) extends Quiver.{v} obj where
  /-- The identity morphism on an object -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g` -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

/-- Notation for the identity morphism in a category -/
notation "𝟙" => DeductiveSystem.id

/-- Notation for composition of morphisms in a category (diagrammatic order) -/
infixr:80 " ≫ " => DeductiveSystem.comp

/-!
### Category

A category is a category structure satisfying three axioms:
identity laws and associativity.
-/

/--
The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will need to be
specified explicitly, as `Category.{v} C`.
-/
class Category (obj : Type u) : Type max u (v + 1) extends DeductiveSystem.{v} obj where
  /-- Identity morphisms are left identities for composition -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  /-- Identity morphisms are right identities for composition -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  /-- Composition in a category is associative -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

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
Monoids: Given a monoid M, we have an associated one object category which we denote by
B M (the 'unlooping' of M)
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

end Cat
