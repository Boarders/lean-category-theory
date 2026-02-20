import CategoryTheory.Category
import CategoryTheory.Contravariant.Functor
import CategoryTheory.Morphisms
import CategoryTheory.Contravariant.NaturalTransformation

universe u₁ u₂ v₁ v₂ u v

namespace Cat
namespace Contravariant

open Quiver
open DeductiveSystem
open Category

structure NaturalIsomorphism (C : Type u₁) [Category C] (D : Type u₂) [Category D] (F G : Contravariant.Functor C D) where
  forward  : Contravariant.NaturalTransformation F G
  backward : Contravariant.NaturalTransformation G F
  iso : forall (c : C) , IsoPair (forward.θ c) (backward.θ c)

end Contravariant
end Cat
