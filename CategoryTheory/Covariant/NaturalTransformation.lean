import CategoryTheory.Category
import CategoryTheory.Covariant.Functor

universe u₁ u₂ v₁ v₂ u v

namespace Cat
namespace Covariant

open Quiver
open DeductiveSystem
open Category

structure NaturalTransformation {C : Type u₁} [Category C] {D : Type u₂} [Category D] (F G : Covariant.Functor C D) where
  θ : ∀ (c : C) , Hom (F.F₀ c) (G.F₀ c)
  naturality : ∀ {c d : C} (f : Hom c d) , F.F₁ f ≫ θ d = θ c ≫ G.F₁ f

end Covariant
end Cat
