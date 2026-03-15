import CategoryTheory.Category
import CategoryTheory.Contravariant.Functor
import CategoryTheory.Morphisms
import CategoryTheory.Contravariant.NaturalIsomorphism
import CategoryTheory.Contravariant.HomFunctor

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

structure IsRepresentable (C : Type u₁) [Category C] (F : Contravariant.Functor C (Type u₁)) where
  obj : C
  iso : Contravariant.NaturalIsomorphism C (Type u₁) F (Contravariant.Representable obj)
