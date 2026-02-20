import CategoryTheory.Category
import CategoryTheory.Covariant.Functor
import CategoryTheory.Morphisms
import CategoryTheory.Covariant.NaturalTransformation

universe u₁ u₂ v₁ v₂ u v

namespace Cat
namespace Covariant

open Quiver
open DeductiveSystem
open Category

structure NaturalIsomorphism (C : Type u₁) [Category C] (D : Type u₂) [Category D] (F G : Covariant.Functor C D) where
  forward  : Covariant.NaturalTransformation F G
  backward : Covariant.NaturalTransformation G F
  iso : forall (c : C) , IsoPair (forward.θ c) (backward.θ c)

end Covariant
end Cat
