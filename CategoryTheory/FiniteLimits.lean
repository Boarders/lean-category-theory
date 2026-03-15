import CategoryTheory.Category
import CategoryTheory.Commutative
import CategoryTheory.Morphisms
import CategoryTheory.Product
import CategoryTheory.Exponential
import CategoryTheory.Equalizer
import CategoryTheory.Pullback

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem

class HasProductsAndEqualizers (c : Type u) extends Category c, HasProducts c, HasEqualizers c

instance (c : Type u) [Category c][HasProducts c] [HasEqualizers c] : HasProductsAndEqualizers c where


/- The pullback:

       a → b
       ↓   ↓ f
       c → d
         g
can be constructed by taking the product of b and c, b × c and then constructing the
equalizer:
                      Pr₁ ≫ f
       Eq f g → b × c========⇉ d
                      Pr₂ ≫ g
-/
def products_equalizers_imply_pullbacks {C : Type u} [Category C] [hPr : HasProducts C] [hEq: HasEqualizers C] : HasPullbacks C := by
  refine {mkPullback := ?_}
  intro b c d g f
  let prod_bc : ProductData b c := hPr.mkProduct b c
  let Pr₁_f : Hom (b × c) d := Pr₁ b c ≫ f
  let Pr₂_g : Hom (b × c) d := Pr₂ b c ≫ g
  let Eq_fg : EqData Pr₁_f Pr₂_g := hEq.mkEqualizer Pr₁_f Pr₂_g
  let i := Eq_fg.univ
  have eq_is_pullback : IsPullback g f (Eq_fg.obj) (i ≫ Pr₁ b c) (i ≫ Pr₂ b c) := by
    let is_Eq := Eq_fg.is_Eq
    refine {commutes := ?_, mediating_morphism := ?_, unique := ?_}
    · simp [CommutativeSquare, i]
      rw [is_Eq.eq]
    · intro T top' left' comm
      let T_bc : Hom T (b × c) := top' ▵ left'
      simp [CommutativeSquare] at comm
      have eq₁ : T_bc ≫ Pr₁_f = top' ≫ f := by
        simp [T_bc, Pr₁_f, <- Category.assoc, fork_β₁]
      have eq₂ : T_bc ≫ Pr₂_g = left' ≫ g := by
        simp [T_bc, Pr₂_g, <- Category.assoc, fork_β₂]
      have eq_commutes : T_bc ≫ Pr₁_f = T_bc ≫ Pr₂_g := by
        rw [eq₁, eq₂, comm]
      let eq_map := is_Eq.mediating_morphism T_bc eq_commutes
      exists eq_map.val
      constructor
      · rw [← Category.assoc, eq_map.property]; simp [T_bc, fork_β₁]
      · rw [← Category.assoc, eq_map.property]; simp [T_bc, fork_β₂]
    · intro T top' left' comm j j_top j_left
      let T_bc : Hom T (b × c) := top' ▵ left'
      simp [CommutativeSquare] at comm
      have eq₁ : T_bc ≫ Pr₁_f = top' ≫ f := by
        simp [T_bc, Pr₁_f, <- Category.assoc, fork_β₁]
      have eq₂ : T_bc ≫ Pr₂_g = left' ≫ g := by
        simp [T_bc, Pr₂_g, <- Category.assoc, fork_β₂]
      have eq_commutes : T_bc ≫ Pr₁_f = T_bc ≫ Pr₂_g := by
        rw [eq₁, eq₂, comm]
      have j_i_eq : j ≫ i = T_bc := by
        apply (product_proof b c).unique top' left'
        · rw [Category.assoc]; exact j_top
        · rw [Category.assoc]; exact j_left
      apply is_Eq.unique T_bc eq_commutes
      exact j_i_eq
  have eq_pullback : PullbackData g f := {
    obj := Eq_fg.obj,
    top := i ≫ Pr₁ b c,
    left := i ≫ Pr₂ b c,
    is_pullback := eq_is_pullback
  }
  exact eq_pullback
