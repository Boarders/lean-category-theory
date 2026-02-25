import CategoryTheory.Category
import CategoryTheory.Commutative
import CategoryTheory.Morphisms

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem

/--
       a → b
       ↓
       c
-/
structure IsProduct {C : Type u}[Category.{v} C] {a b c : C} (proj₁ : Hom a b) (proj₂ : Hom a c) where
  mediating_morphism : ∀ {a' : C}
    (proj₁' : Hom a' b) (proj₂' : Hom a' c),
    {i : Hom a' a // i ≫ proj₁ = proj₁' ∧ i ≫ proj₂ = proj₂'}
  unique : ∀ {a' : C} (proj₁' : Hom a' b) (proj₂' : Hom a' c)
    (j : Hom a' a), j ≫ proj₁ = proj₁' → j ≫ proj₂ = proj₂' →
    j = (mediating_morphism proj₁' proj₂').val

structure ProductData {C : Type u} [Category C] (b c : C) where
  obj : C
  proj₁ : Hom obj b
  proj₂ : Hom obj c
  is_product : IsProduct proj₁ proj₂

/--
When we say a category has all products, we mean that there is some specific choice
of product strcuture for each pair of objects.
-/
class HasProducts (C : Type u)[Category C] where
  mkProduct : ∀ (c d : C), ProductData c d

def product_obj {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : C :=
  (hp.mkProduct b c).obj

/-- Notation for composition of morphisms in a category (diagrammatic order) -/
infixr:60 " × " => product_obj

def product_proj₁ {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : Hom (product_obj b c) b :=
  (hp.mkProduct b c).proj₁

def product_proj₂ {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : Hom (product_obj b c) c :=
  (hp.mkProduct b c).proj₂

/-- Notation for projection maps -/
notation "Pr₁" => product_proj₁
notation "Pr₂" => product_proj₂

def product_proof {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : IsProduct (Pr₁ b c) (Pr₂ b c) :=
  (hp.mkProduct b c).is_product

def fork {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : Hom x (a × b) :=
  ((product_proof a b).mediating_morphism f g)

/-- Use algebra of programming notation ▵ for fork map to a product -/
infix:80 " ▵ " => fork

theorem fork_β  {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : (f ▵ g) ≫ Pr₁ a b = f ∧ (f ▵ g) ≫ Pr₂ a b = g := by
  simp [fork]
  exact ((product_proof a b).mediating_morphism f g).property

@[simp] theorem fork_β₁  {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : (f ▵ g) ≫ Pr₁ a b = f := by
  apply And.left
  apply fork_β f g

@[simp] theorem fork_β₂  {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : (f ▵ g) ≫ Pr₂ a b = g := by
  apply And.right
  apply fork_β f g

def product {C : Type u}[Category C] [hp : HasProducts C] {a b c d : C}
  (f : Hom a c) (g : Hom b d) : Hom (a × b) (c × d) :=
  let proj₁' := (product_proj₁ a b) ≫ f
  let proj₂' := (product_proj₂ a b) ≫ g
  ((product_proof c d).mediating_morphism proj₁' proj₂')

/-- Use algebra of programming notation □ for product map -/
infix:80 " □ " => product
