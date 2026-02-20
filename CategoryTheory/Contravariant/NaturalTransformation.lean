import CategoryTheory.Category
import CategoryTheory.Contravariant.Functor

universe u₁ u₂ v₁ v₂ u v

namespace Cat
namespace Contravariant

open Quiver
open DeductiveSystem
open Category

structure NaturalTransformation {C : Type u₁} [Category C] {D : Type u₂} [Category D] (F G : Contravariant.Functor C D) where
  θ : ∀ (c : C) , Hom (F.F₀ c) (G.F₀ c)
  naturality : ∀ {c d : C} (f : Hom c d) , F.F₁ f ≫ θ c = θ d ≫ G.F₁ f

end Contravariant
end Cat
