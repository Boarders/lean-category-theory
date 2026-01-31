import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver

structure Functor (C : Type u₁) [Category C] (D : Type u₂) [Category D] where
  F₀ : C → D
  F₁ : ∀ {c₁ c₂ : C}, Quiver.Hom c₁ c₂ → Quiver.Hom (F₀ c₁) (F₀ c₂)
