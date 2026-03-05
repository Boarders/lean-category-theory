import Mathlib
import CategoryTheory.Category
import CategoryTheory.Morphisms
import CategoryTheory.Product
import CategoryTheory.Exponential
import CategoryTheory.Equalizer
import CategoryTheory.Limit
import CategoryTheory.TerminalObject
import CategoryTheory.InitialObject

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem

class IsCartesianClosed (C : Type u) extends Category.{v} C, HasProducts C, HasExponentials C, HasTerminalObject C

def IsDegenerate (C : Type u) [IsCartesianClosed C] := ∀ {c d : C}(f g : Hom c d), f = g

theorem ccc_zero_object {C : Type u}
    [IsCartesianClosed C] [HasInitialObject C]
    (zero_iso : IsIso (!ℂ0 (ℂ1 : C))) : IsDegenerate C := by
  intro c d f g
  let ⟨i, iso⟩ := one_prod_iso c
  have hom_triv : Hom c d ≃ Hom ℂ0 (c ~> d) := by
    calc
      Hom c d ≃ Hom (ℂ1 × c) d := (iso_hom i iso)
      _       ≃ Hom ℂ1 (c ~> d) := exponentialAdjoint ℂ1 c d
      _       ≃ Hom ℂ0 (c ~> d) := (iso_hom (!ℂ0 ℂ1) zero_iso).symm
  haveI : Unique (Hom ℂ0 (c ~> d)) := Hom_init_Unqiue (c ~> d)
  haveI : Unique (Hom c d) := Equiv.unique hom_triv
  exact Subsingleton.elim f g
