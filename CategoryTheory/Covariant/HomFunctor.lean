import CategoryTheory.Category
import CategoryTheory.Covariant.Functor

universe u₁ u₂ v₁ v₂ u v

namespace Cat
namespace Covariant

open Quiver
open DeductiveSystem
open Category

def Representable {C : Type u} [Category C] (c : C) : Covariant.Functor C (Type u) := by
  refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · intro c'
    exact (Hom c c')
  · intro c1 c2 f g
    exact g ≫ f
  · intro c
    funext g
    simp [comp_id]
    rfl
  · intro c d e f g
    funext g
    rw [<- assoc]
    rfl

end Covariant
end Cat
