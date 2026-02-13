import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver

def CommutativeSquare {C : Type u} [Category C] {a b c d : C}
  (top : Hom a b) (right : Hom b d) (left : Hom a c) (bottom : Hom c d) : Prop :=
  top ≫ right = left ≫ bottom
