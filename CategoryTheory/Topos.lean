import CategoryTheory.Category
import CategoryTheory.Morphisms
import CategoryTheory.Product
import CategoryTheory.Exponential
import CategoryTheory.Equalizer
import CategoryTheory.Limit
import CategoryTheory.TerminalObject
import CategoryTheory.InitialObject
import CategoryTheory.CartesianClosedCategory
import CategoryTheory.SubobjectClassifier

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem

class IsTopos (C : Type u) extends Category.{v} C, IsCartesianClosed C, HasInitialObject C, HasSubobjectClassifier C


def IsWellPointed (C : Type u) [IsTopos C] :=
  ∀ {c d : C} (f g : Hom c d) , ∀ (global : Hom ℂ1 c),
  (global ≫ f) = (global ≫ g) -> f = g
