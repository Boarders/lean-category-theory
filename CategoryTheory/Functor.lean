import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Functor

structure Functor (C : Type u₁) [Category C] (D : Type u₂) [Category D] where
  F₀ : C → D
  F₁ : ∀ {c₁ c₂ : C}, Hom c₁ c₂ → Hom (F₀ c₁) (F₀ c₂)
  F_id : ∀ {c : C}, F₁ (id c) = (DeductiveSystem.id (F₀ c))
  F_comp : ∀ {c : C}
