import CategoryTheory.Category
import CategoryTheory.Commutative

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver

structure IsPullback {C : Type u}[Category.{v} C] {b c d : C} (bottom : Hom c d) (right : Hom b d) (obj : C) (top : Hom obj b) (left : Hom obj c) : Type (max v u) where
  commutes : CommutativeSquare top right left bottom
  mediating_morphism : ∀ {a : C}
    (top' : Hom a b) (left' : Hom a c)
    (_commutes' : CommutativeSquare top' right left' bottom),
    ∃! (i : Hom a obj) , i ≫ top = top' ∧ i ≫ left = left'

/--
       T
       ├───────────┐
       │           ↓
       │   a → b → c
       │   ↓   ↓   ↓
       └───d → e → f

If the LHS and the RHS are pullbacks then the overall square is a pullback
-/
def PBL_outer {C : Type u}{a b c d e f : C} [Category C]
  (ab : Hom a b) (bc : Hom b c)
  (ad : Hom a d) (be : Hom b e) (cf : Hom c f)
  (de : Hom d e) (ef : Hom e f)
  (rhs_pullback : IsPullback ef cf b bc be)
  (lhs_pullback : IsPullback de be a ab ad) :
  IsPullback (de ≫ ef) cf a (ab ≫ bc) ad := by
  refine {commutes := ?_, mediating_morphism := ?_}
  · simp [CommutativeSquare]
    -- need to show: ab ≫ bc ≫ cf = ad ≫ de ≫ ef
    have eq_1 : ab ≫ bc ≫ cf = ab ≫ be ≫ ef := by
      rw [rhs_pullback.commutes]
    have eq_2 : ab ≫ be ≫ ef = ad ≫ de ≫ ef := by
      rw [<- Category.assoc, lhs_pullback.commutes]
      rw [Category.assoc]
    trans (ab ≫ be ≫ ef)
    · exact eq_1
    · exact eq_2
  · intro T Tc Td T_commSq
    have Tb : ∃! (i : Hom T b) , i ≫ bc = Tc ∧ i ≫ be = Td ≫ de  := by
      apply rhs_pullback.mediating_morphism
      simp [CommutativeSquare]
      rw [T_commSq]
    have map_to_a : ∃! (i : Hom T a) , i ≫ ab = Tb.fst ∧ i ≫ ad = Td  := by
      apply lhs_pullback.mediating_morphism
      simp [CommutativeSquare]
    have Ta : ∃! i, i ≫ ab ≫ bc = Tc ∧ i ≫ ad = Td  := by
      cases map_to_a with
      | intro i P =>
        exists i
        constructor
        · simp
        · intro Ta'
          simp
    exact Ta
