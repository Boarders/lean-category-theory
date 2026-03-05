import CategoryTheory.Category
import CategoryTheory.Morphisms

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver

structure IsInitial {C : Type u}[Category.{v} C] (init : C) : Type (max v u) where
  from_init : ∀ (c : C) , Hom init c
  uniq_init : ∀ {c : C} (f : Hom init c) , from_init c = f

/-- Notation for the initial object -/

notation "!0" => IsInitial.from_init
notation "!0-uniq" => IsInitial.uniq_init

structure InitialData (C : Type u)[Category.{v} C] : Type (max v u) where
  object : C
  from_initial : ∀ (c : C) , Hom object c
  uniq_initial : ∀ {c : C} (f : Hom object c) , from_initial c = f

class HasInitialObject (C : Type u)[S : Category C] where
  get_initial : InitialData C

abbrev initial_object {C : Type u} [S : Category C] [HasInitialObject C] : C :=
  HasInitialObject.get_initial.object

notation "ℂ0" => initial_object

abbrev initial_map {C : Type u} [S : Category C] [HasInitialObject C] (c : C) : Hom initial_object c :=
  HasInitialObject.get_initial.from_initial c

notation "!ℂ0" => initial_map

abbrev initial_uniq {C : Type u} [S : Category C] [HasInitialObject C] {c : C}(f : Hom ℂ0 c) : !ℂ0 c = f :=
  HasInitialObject.get_initial.uniq_initial _

notation "!ℂ0_uniq" => initial_uniq

lemma init_endo_id [Category.{v} C] {init : C}
  {f g : Hom init init} (is_init : IsInitial init) :
  f = g := by
  rw [<- is_init.uniq_init f, is_init.uniq_init g]

/--
Show that an initial object in a category is unqiue up to unique isomorphism
 -/
def InitialUnique {C : Type u}[Category.{v} C] (init₁ init₂ : C)
  (is_init₁ : IsInitial init₁) (is_init₂ : IsInitial init₂) :
  Σ' (f : Hom init₁ init₂) , IsIso f ×' (∀ (g : Hom init₁ init₂) , g = f) :=  by
  have i₁_i₂ : Hom init₁ init₂ := is_init₁.from_init init₂
  have i₂_i₁ : Hom init₂ init₁ := is_init₂.from_init init₁
  have i₁_roundtrip : i₁_i₂ ≫ i₂_i₁ = (𝟙 init₁) := by
    apply init_endo_id is_init₁
  have i₂_roundtrip : i₂_i₁ ≫ i₁_i₂ = (𝟙 init₂) := by
    apply init_endo_id is_init₂
  exists i₁_i₂
  · constructor
    · refine {inv := ?_, post_inv := ?_, pre_inv := ?_}
      · exact i₂_i₁
      . exact i₂_roundtrip
      . exact i₁_roundtrip
    · intro g
      -- Show that:
      --   g = i₁_i₂
      -- by showing both are equal to !0[i₁]
      rw [<- is_init₁.uniq_init g, <- is_init₁.uniq_init i₁_i₂]


def Hom_init_Unqiue {C : Type u} [Category C] [HasInitialObject C] (c : C) : Unique (Hom ℂ0 c) := by
  refine {default := ?_, uniq := ?_}
  · exact !ℂ0 c
  · intro f
    symm
    apply !ℂ0_uniq
