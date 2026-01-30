import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat

structure Functor (C : Type u₁) [Category C] (D : Type u2) [Category D] where
  F₀ : C → D
