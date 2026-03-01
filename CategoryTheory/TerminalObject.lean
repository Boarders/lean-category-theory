import CategoryTheory.Category
import CategoryTheory.Morphisms

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver

structure IsTerminal {C : Type u}[Category.{v} C] (term : C) : Type (max v u) where
  to_term : ∀ (c : C) , Hom c term
  uniq_term : ∀ {c : C} (f : Hom c term) , to_term c = f

structure TerminalData (C : Type u)[Category.{v} C] : Type (max v u) where
  object : C
  to_term : ∀ (c : C) , Hom c object
  uniq_term : ∀ {c : C} (f : Hom c object) , to_term c = f

class HasTerminalObject (C : Type u)[S : Category C] where
  get_terminal : TerminalData C

abbrev terminal_object {C : Type u} [S : Category C] [HasTerminalObject C] : C :=
  HasTerminalObject.get_terminal.object

notation "ℂ1" => terminal_object

abbrev terminal_map {C : Type u} [S : Category C] [HasTerminalObject C] (c : C) : Hom c terminal_object :=
  HasTerminalObject.get_terminal.to_term c

notation "!ℂ1" => terminal_map

abbrev terminal_uniq {C : Type u} [S : Category C] [HasTerminalObject C] {c : C}(f : Hom c ℂ1) : !ℂ1 c = f :=
  HasTerminalObject.get_terminal.uniq_term _

notation "!ℂ1_uniq" => terminal_uniq

instance : HasTerminalObject (Type u) where
  get_terminal := by
    refine {object := ?_, to_term := ?_, uniq_term := ?_}
    · exact ULift Unit
    · exact fun _C _c => ULift.up ()
    · intro c f
      rfl

/-- Notation for the terminal object -/
notation "!" => IsTerminal.to_term
notation "!-uniq" => IsTerminal.uniq_term

lemma term_endo_id [Category.{v} C] {term : C}
  {f g : Hom term term} (is_terminal : IsTerminal term) :
  f = g := by
  rw [<- is_terminal.uniq_term f, is_terminal.uniq_term g]

/--
Show that an terminal object in a category is unqiue up to unique isomorphism
 -/
def TerminalUnique {C : Type u}[Category.{v} C] (term₁ term₂ : C)
  (is_term₁ : IsTerminal term₁) (is_term₂ : IsTerminal term₂) :
  Σ' (f : Hom term₁ term₂) , IsIso f ×' (∀ (g : Hom term₁ term₂) , g = f) :=  by
  have i₁_i₂ : Hom term₁ term₂ := is_term₂.to_term term₁
  have i₂_i₁ : Hom term₂ term₁ := is_term₁.to_term term₂
  have i₁_roundtrip : i₁_i₂ ≫ i₂_i₁ = (𝟙 term₁) := by
    apply term_endo_id is_term₁
  have i₂_roundtrip : i₂_i₁ ≫ i₁_i₂ = (𝟙 term₂) := by
    apply term_endo_id is_term₂
  exists i₁_i₂
  · constructor
    · refine {inv := ?_, post_inv := ?_, pre_inv := ?_}
      · exact i₂_i₁
      . exact i₂_roundtrip
      . exact i₁_roundtrip
    · intro g
      -- Show that:
      --   g = i₁_i₂
      -- by showing both are equal to ![i₁]
      rw [<- is_term₂.uniq_term g, <- is_term₂.uniq_term i₁_i₂]
