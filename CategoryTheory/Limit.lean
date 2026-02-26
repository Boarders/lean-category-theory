import CategoryTheory.Category
import CategoryTheory.Commutative
import CategoryTheory.Morphisms
import CategoryTheory.Covariant.Functor

universe u₁ u₂ v₁ v₂ u v i j

namespace Cat
open Quiver
open DeductiveSystem
open Covariant

structure Cone {I : Type i} [Category I] {C : Type u} [Category C] (F : Functor I C) where
  obj : C
  C₀ : ∀ (i : I), Hom obj (F.F₀ i)
  commutes : ∀ (i j : I), (f : Hom i j) → C₀ i ≫ F.F₁ f = C₀ j

structure UniversalCone {I : Type i}  [Category I] {C : Type u} [Category C] (F : Functor I C) extends Cone F where
  mediating : ∀ (cone' : Cone F) ,
    {u : Hom cone'.obj obj // ∀ (i : I) , cone'.C₀ i = u ≫ C₀ i}
  univ : ∀ (cone' : Cone F)
    (u' : Hom cone'.obj obj), (∀ (i : I) , cone'.C₀ i = u' ≫ C₀ i) →
       u' = (mediating cone').val

class HasShapeLimits (I : Type i) [Category I] (C : Type u) [Category C] where
  mkLimit : ∀ (F : Functor I C), UniversalCone F

def mediating_endo {I : Type i} [Category I] {C : Type u}[Category C] (F : Functor I C)
  (UC : UniversalCone F) (f : Hom UC.obj UC.obj) :
  (∀ (i : I), UC.C₀ i = f ≫ UC.C₀ i) → (𝟙 UC.obj) = f := by
  intro f_mediates
  have mediate_eq_id : (𝟙 UC.obj) = (UC.mediating UC.toCone).val := by
    apply UC.univ UC.toCone (𝟙 UC.obj)
    intro i
    simp
  have mediate_eq_f :  (UC.mediating UC.toCone).val = f := by
    symm
    apply UC.univ UC.toCone f
    exact f_mediates
  trans (UC.mediating UC.toCone).val
  · exact mediate_eq_id
  · exact mediate_eq_f


def limits_unique {I : Type i} [Category I] {C : Type u}[Category C] (F : Functor I C)
  (UC UC' : UniversalCone F) :
  Unique { m : Hom UC.obj UC'.obj // IsIso' m ∧ ∀ (i : I),
    UC.C₀ i = m ≫ UC'.C₀ i } := by
  refine {default := ?_, uniq := ?_}
    -- first show that there is a mediating iso between the two cones
  · let mediating := UC.mediating UC'.toCone
    let mediating' := UC'.mediating UC.toCone
    let to_from := mediating.val ≫ mediating'.val
    let from_to := mediating'.val ≫ mediating.val
    have to_from_eq : to_from = (𝟙 _) := by
      symm
      apply mediating_endo F UC' to_from
      intro i
      simp [to_from]
      rw [<- mediating'.prop i, <- mediating.prop i]
    have from_to_eq : from_to = (𝟙 _) := by
      symm
      apply mediating_endo F UC from_to
      intro i
      simp [from_to]
      rw [<- mediating.prop i, <- mediating'.prop i]
    exact ⟨mediating'.val, ⟨mediating.val, to_from_eq, from_to_eq⟩, mediating'.prop⟩
    -- then show that any other map with these properties is the same
    -- morphism using the uniqueness of the induced map
  · intro ⟨uc_uc', _, mediates⟩
    apply Subtype.ext
    apply UC'.univ UC.toCone uc_uc' mediates
