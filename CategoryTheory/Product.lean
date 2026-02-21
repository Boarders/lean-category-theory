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
structure IsProduct {C : Type u}[Category.{v} C] {a b c : C} (proj₁ : Hom a b) (proj₂ : Hom a c) : Prop where
  mediating_morphism : ∀ {a' : C}
    (proj₁' : Hom a' b) (proj₂' : Hom a' c),
    ∃! (i : Hom a' a) , i ≫ proj₁ = proj₁' ∧ i ≫ proj₂ = proj₂'

structure ProductData {C : Type u} [Category C] (b c : C) where
  obj : C
  proj₁ : Hom obj b
  proj₂ : Hom obj c
  is_product : IsProduct proj₁ proj₂

/--
When we say a category has all products, we mean that there is some specific choice
of product for each pair of objects.
-/
class HasProducts (C : Type u)[Category C] where
  mkProduct : ∀ (c d : C), ProductData c d

def product_obj {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : C :=
  (hp.mkProduct b c).obj

def product_proj₁ {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : Hom (product_obj b c) b :=
  (hp.mkProduct b c).proj₁

def product_proj₂ {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : Hom (product_obj b c) c :=
  (hp.mkProduct b c).proj₂

def product_proof {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : IsProduct (product_proj₁ b c) (product_proj₂ b c) :=
  (hp.mkProduct b c).is_product
