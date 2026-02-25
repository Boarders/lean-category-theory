import CategoryTheory.Morphisms
import Mathlib.Logic.ExistsUnique

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem

/--

                  f
       Eq f g → a ⇉ b
                  g

-/

structure IsEq {C : Type u}[Category.{v} C] {a b : C} (f g : Hom a b)(Eq : C) (univ : Hom Eq a) where
  eq : univ ≫ f = univ ≫ g
  mediating_morphism : ∀ {T : C}
    (i : Hom T a) , (i ≫ f) = (i ≫ g) →
    {mediate : Hom T Eq // mediate ≫ univ = i}
  unique : ∀ {T : C} (i : Hom T a) (h : i ≫ f = i ≫ g)
    (j : Hom T Eq), j ≫ univ = i →
    j = (mediating_morphism i h).val

structure EqData {C : Type u} [Category C] {a b : C} (f g : Hom a b) where
  obj : C
  univ : Hom obj a
  is_Eq : IsEq f g obj univ

/--
When we say a category has all equalizers, we mean that there is some specific choice
of equalizer structure for each pair of parallel morphisms.
-/
class HasEqualizers (C : Type u)[Category C] where
  mkEqualizer : ∀ {a b : C} (f g : Hom a b), EqData f g


def equalizer_obj {C : Type u}[Category C] [hp : HasEqualizers C]
  {a b : C}(f g : Hom a b) : C :=
  (hp.mkEqualizer f g).obj

/-- Notation for choice of equalizer object in a cat with equalizers -/
notation "Eq" => equalizer_obj

def equalizer_map {C : Type u}[Category C] [hp : HasEqualizers C]
  {a b : C}(f g : Hom a b) : Hom (Eq f g) a :=
  (hp.mkEqualizer f g).univ

/-- Notation for universal morphism from equalizer -/
notation "Eq₁" => equalizer_map

def equalizer_property {C : Type u}[Category C] [hp : HasEqualizers C]
  {a b : C}(f g : Hom a b) : IsEq f g (Eq f g) (Eq₁ f g)  :=
  (hp.mkEqualizer f g).is_Eq
