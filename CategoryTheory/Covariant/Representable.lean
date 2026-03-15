import CategoryTheory.Category
import CategoryTheory.Covariant.Functor
import CategoryTheory.Morphisms
import CategoryTheory.Covariant.NaturalIsomorphism
import CategoryTheory.Covariant.HomFunctor

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

structure IsRepresentable (C : Type u₁) [Category C] (F : Covariant.Functor C (Type u₁)) where
  obj : C
  iso : Covariant.NaturalIsomorphism C (Type u₁) F (Covariant.Representable obj)
