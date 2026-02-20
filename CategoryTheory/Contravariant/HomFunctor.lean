import CategoryTheory.Category
import CategoryTheory.Contravariant.Functor

universe u₁ u₂ v₁ v₂ u v

namespace Cat
namespace Contravariant

open Quiver
open DeductiveSystem
open Category

def Representable {C : Type u} [Category C] (c : C) : Contravariant.Functor C (Type u) := by
  refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · intro c'
    exact (Hom c' c)
  · intro c1 c2 f g
    exact f ≫ g
  · intro c
    funext g
    simp [id_comp]
    rfl
  · intro c d e f g
    funext g
    rw [assoc]
    rfl

end Contravariant
end Cat
