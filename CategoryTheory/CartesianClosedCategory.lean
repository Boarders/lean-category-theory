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

class IsCartesianClosed (C : Type u) extends Category C, HasProducts C, HasExponentials C, HasTerminalObject C

def IsDegenerate (C : Type u) [IsCartesianClosed C] := ∀ {c d : C}(f g : Hom c d), f = g

theorem ccc_zero_object {C : Type u} [IsCartesianClosed C] [HasInitialObject C] (zero_iso : IsIso (!ℂ0 (ℂ1 : C))) : IsDegenerate C := by
  intro c d f g
  have hom_triv : Hom c d ≃ Unit := by
    calc
      Hom c d ≃ Hom (ℂ1 × c) d := by sorry
      _       ≃ Hom ℂ1 (c ~> d) := by exponentialAdjoint
      _       ≃ Hom ℂ0 (c ~> c) := by iso_hom zero_iso
      _       ≃ Unit := by sorry
  have hom_subsingleton : Subsingleton (Hom c d) := hom_triv.subsingleton
  exact Subsingleton.elim f g
