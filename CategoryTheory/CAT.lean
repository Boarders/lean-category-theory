import CategoryTheory.Category
import CategoryTheory.Covariant.Functor
import CategoryTheory.Morphisms
import CategoryTheory.Constructions

universe v u

namespace Cat
/--
The category of categories of a certain level
  · Obj: Algebraic objects
  · Mor: homomorphisms
-/

structure CAT : Type (u + 1) where
  (α : Type u)
  str: SmallCategory α

def mkCAT (C : Type u) [S: Category C] : CAT :=
  {α := C, str := S}

instance (C : CAT) : Category C.α := C.str

instance : Quiver CAT where
  Hom M N := Covariant.Functor M.α N.α

instance : DeductiveSystem CAT where
  id M := by
    simp [Quiver.Hom]
    apply Covariant.Id_Functor

  comp := Covariant.Comp_Functor

instance CATCategory : Category CAT where
  id_comp := by
    intro C D F
    simp [DeductiveSystem.comp, Covariant.Comp_Functor]
    apply Covariant.Functor.ext
    simp [DeductiveSystem.id, Covariant.Comp_Hom, Covariant.Id_Functor, Covariant.Id_Hom]
    simp [Covariant.Comp_Hom]
    funext c₁ c₂
    simp [DeductiveSystem.id, Covariant.Id_Functor, Covariant.Id_Hom]

  comp_id := by
    intro C D F
    simp [DeductiveSystem.comp, Covariant.Comp_Functor]
    apply Covariant.Functor.ext
    simp [DeductiveSystem.id, Covariant.Comp_Hom, Covariant.Id_Functor, Covariant.Id_Hom]
    simp [Covariant.Comp_Hom]
    funext c₁ c₂
    simp [DeductiveSystem.id, Covariant.Id_Functor, Covariant.Id_Hom]

  assoc := by
    intro M N P Q f g h
    simp [DeductiveSystem.comp, Covariant.Comp_Functor]
    apply Covariant.Functor.ext
    simp [Covariant.Comp_Hom]
    · rfl
    · simp [Covariant.Comp_Hom]
      funext c₁ c₂
      rfl

def CategoryIso {C D : Type u} [Category.{u} C] [Category D] (F : Covariant.Functor C D) : Type u :=
  @IsIso CAT CATCategory (mkCAT C) (mkCAT D) F


/--
Example of an iso of categories, between Rel and Rel^op
-/

def flipRel {A : Type u₁}{B : Type u₂} (R : A → B → Prop) : B → A → Prop :=
  fun b a => R a b

def RelToRelOpFunctor : Covariant.Functor Rel.{u} (Opposite Rel.{u}) := by
  refine { F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · intro C
    exact {obj := C}
  · intro _A _B  R
    exact (flipRel R)
  · intro c
    funext c d
    simp [flipRel, DeductiveSystem.id]
    constructor
    · intro eq; rw [eq]
    · intro eq; rw [eq]
  · intro a b c R₁ R₂
    simp [DeductiveSystem.comp]
    funext x z
    simp [flipRel]
    constructor
    · intro ex
      cases ex with
      | intro y pf =>
        exists y
        constructor
        · exact (And.right pf)
        · exact (And.left pf)
    · intro ex
      cases ex with
      | intro y pf =>
        exists y
        constructor
        · exact (And.right pf)
        · exact (And.left pf)

/--
Note: THis is essentially identical to RelToRelOpFunctor, we should
figure out the correct abstraction where we don't need to copy the
construction
-/
def RelOpToRelFunctor : Covariant.Functor (Opposite Rel.{u}) (Rel.{u}) := by
  refine { F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · intro C
    exact C.obj
  · intro _A _B  R
    exact (flipRel R)
  · intro c
    funext c d
    simp [flipRel, DeductiveSystem.id]
    constructor
    · intro eq; rw [eq]
    · intro eq; rw [eq]
  · intro a b c R₁ R₂
    simp [DeductiveSystem.comp]
    funext x z
    simp [flipRel]
    constructor
    · intro ex
      cases ex with
      | intro y pf =>
        exists y
        constructor
        · exact (And.right pf)
        · exact (And.left pf)
    · intro ex
      cases ex with
      | intro y pf =>
        exists y
        constructor
        · exact (And.right pf)
        · exact (And.left pf)


def RelToRelOpIso : CategoryIso RelToRelOpFunctor := by
  refine { inv := ?_, pre_inv := ?_, post_inv := ?_}
  · exact RelOpToRelFunctor
  · apply Covariant.Functor.ext
    · simp [RelToRelOpFunctor, RelOpToRelFunctor, DeductiveSystem.comp, Covariant.Comp_Functor, Covariant.Comp_Hom]
      funext C
      rfl
    · constructor
  · apply Covariant.Functor.ext
    · simp [RelToRelOpFunctor, RelOpToRelFunctor, DeductiveSystem.comp, Covariant.Comp_Functor, Covariant.Comp_Hom]
      funext C
      rfl
    · constructor
