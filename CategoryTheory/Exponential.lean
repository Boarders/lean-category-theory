import CategoryTheory.Category
import CategoryTheory.Commutative
import CategoryTheory.Morphisms
import CategoryTheory.Product

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem

/--
       c × a
       │    ╲
   ⟨λf,id⟩    f
       ↓       ↘
     b^a × a ──→ b
            eval
-/
structure Exponential {C : Type u} [Category C] [HasProducts C] (a b : C) where
  obj : C
  eval : Hom (obj × α) b
  adj  : ∀ {c : C} (_f : (c × a) ⇒ b), (c ⇒ obj)
  β : ∀ {c : C} (f : (c × a) ⇒ b) , ((adj f) □ (𝟙 a)) ≫ eval = f
  uniq :
    ∀ {c : C} (f : (c × a) ⇒ b) (adj_f' : c ⇒ obj) ,
      (((adj_f') □ (𝟙 a)) ≫ eval = f) -> adj_f' = adj f

-- Any map into a function object is equivalent to a lambda
theorem eta  {C : Type u} [Category C] [HasProducts C] {a b c : C}
  (Exp : Exponential a b) (f : c ⇒ Exp.obj) :
  (Exp.adj ((f □ (𝟙 a)) ≫ Exp.eval)) = f := by
  symm
  apply Exp.uniq ((f □ (𝟙 a)) ≫ Exp.eval) f
  rfl


/--
When we say a category has all exponentials, we mean that there is some specific choice
of exponential object and sructure maps for each pair of objects.
-/
class HasExponentials (C : Type u)[Category C] [HasProducts C] where
  mkExponential : ∀ (c d : C), Exponential c d

-- def exponential_obj {C : Type u}[Category C] [HasProducts C] [hp : HasExponentials C]
--   (b c : C) : C :=
--   (hp.mkExponential b c).obj

-- def exponential_proj₁ {C : Type u}[Category C]  [HasProducts C] [hp : HasExponentials C]
--   (b c : C) : Hom (exponential_obj b c) b :=
--   (hp.mkExponential b c).proj₁

-- def exponential_proj₂ {C : Type u}[Category C] [HasProducts C] [hp : HasExponentials C]
--   (b c : C) : Hom (exponential_obj b c) c :=
--   (hp.mkExponential b c).proj₂

-- def exponential_proof {C : Type u}[Category C]  [HasProducts C] [hp : HasExponentials C]
--   (b c : C) : IsExponential (exponential_proj₁ b c) (exponential_proj₂ b c) :=
--   (hp.mkExponential b c).is_exponential
