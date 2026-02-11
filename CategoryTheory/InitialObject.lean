import CategoryTheory.Category
import CategoryTheory.Functor
import CategoryTheory.Morphisms

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver

structure IsInitial {C : Type u}[Category.{v} C] (init : C) : Type (max v u) where
  from_init : ∀ (c : C) , Hom init c
  uniq_init : ∀ {c : C} (f : Hom init c) , from_init c = f

/-- Notation for the initial object -/
notation "!" => IsInitial.from_init
notation "!-uniq" => IsInitial.uniq_init

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
    · refine {inv := ?_, l_inv := ?_, r_inv := ?_}
      · exact i₂_i₁
      . exact i₂_roundtrip
      . exact i₁_roundtrip
    · intro g
      -- Show that:
      --   g = i₁_i₂
      -- by showing both are equal to ![i₁]
      rw [<- is_init₁.uniq_init g, <- is_init₁.uniq_init i₁_i₂]
