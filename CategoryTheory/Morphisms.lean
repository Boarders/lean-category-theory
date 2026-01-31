import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category


structure IsIso {C : Type u} [Category C] {a b : C} (f : Hom a b) where
  inv : Hom b a
  -- Note: Because we use diagrammatic order, these are the opposite
  -- of the usual left inverse and right inverse laws
  l_inv : (inv ≫ f) = (𝟙 b)
  r_inv : (f ≫ inv) = (𝟙 a)

open IsIso

theorem uniq_inv
   {C : Type u} {a b : C} [Category C] (f : Hom a b) (g₁ g₂ : IsIso f) :
    g₁.inv = g₂.inv
  := by
  have h₁ :  g₁.inv = g₁.inv ≫ (f ≫ g₂.inv) := by {
    rw [g₂.r_inv]
    simp
  }
  rw [h₁]
  rw [<- assoc, l_inv]
  simp
