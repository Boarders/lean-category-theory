import CategoryTheory.Category
import CategoryTheory.Functor

universe v u

namespace Cat
/--
The category of categories of a certain level
  · Obj: Algebraic objects
  · Mor: homomorphisms

We show this in the case of the category of monoids
-/

structure CAT : Type (u + 1) where
  (α : Type u)
  str: Category α

instance (C : CAT) : Category C.α := C.str

instance : Quiver CAT where
  Hom M N := Functor M.α N.α

instance : DeductiveSystem CAT where
  id M := by
    simp [Quiver.Hom]
    apply Id_Functor

  comp := Comp_Functor

instance : Category CAT where
  id_comp := by
    intro M N f
    simp [DeductiveSystem.comp, Comp_Functor]
    cases

    intro m
    simp [DeductiveSystem.id, id_hom]

  comp_id := by
    intro M N f
    simp [DeductiveSystem.comp, comp_hom]
    apply CategoryHom.ext
    intro m
    simp [DeductiveSystem.id, id_hom]

  assoc := by
    intro M N P f g h
    simp [DeductiveSystem.comp, comp_hom]
