import CategoryTheory.Category
import CategoryTheory.Commutative
import CategoryTheory.Morphisms
import CategoryTheory.Covariant.Functor
import CategoryTheory.Limit
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem
open Covariant

/--
       a → b
       ↓
       c
-/

abbrev ProductDiagram := Disc (Fin 2)
def product_hom {C : Type u} [Category C] : (Functor ProductDiagram C) ≃ C × C := by
  refine {toFun := ?_, invFun :=?_, right_inv := ?_, left_inv := ?_}
  · intro F
    exact ⟨F.F₀ {el := 0}, F.F₀ {el := 1}⟩
  · intro pr_C
    rcases pr_C with ⟨c₀, c₁⟩
    refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
    · intro ⟨i⟩
      match i with
      | 0 => exact c₀
      | 1 => exact c₁
    · intro n m eq
      subst eq
      exact DeductiveSystem.id _
    · intro ⟨i⟩
      match i with
      | 0 => rfl
      | 1 => rfl
    · intro i j k eq₁ eq₂
      subst eq₁
      subst eq₂
      simp
      rfl
  · intro ⟨⟨F₀, F₁⟩, F_id, F_comp⟩
    simp
    -- proof that it is left inverse on objects
    have h₀ : ∀ (n : ProductDiagram),
      (match n.el with | (0 : Fin 2) => F₀ ⟨0⟩ | 1 => F₀ ⟨1⟩) = F₀ n := by
      intro ⟨i⟩; match i with | 0 => rfl | 1 => rfl
    simp [h₀]
    congr! with n n' hnn m m' hmm eq eq' heq
    subst hnn; subst hmm
    have : eq = eq' := Subsingleton.elim _ _
    subst this
    subst eq
    -- need to show HEq between the identity at on the match function evaluted at name
    -- and F₁ 𝟙
    --   - First the match statement using h₀ to be 𝟙 (F₀ n)
    --   - Then we can use that F preserves identity
    apply HEq.trans (congr_arg_heq DeductiveSystem.id (h₀ n))
    apply heq_of_eq
    exact F_id.symm
  · intro ⟨c₀, c₁⟩
    rfl









structure IsProduct {C : Type u}[Category.{v} C] {a b c : C} (proj₁ : Hom a b) (proj₂ : Hom a c) where
  mediating_morphism : ∀ {a' : C}
    (proj₁' : Hom a' b) (proj₂' : Hom a' c),
    {i : Hom a' a // i ≫ proj₁ = proj₁' ∧ i ≫ proj₂ = proj₂'}
  unique : ∀ {a' : C} (proj₁' : Hom a' b) (proj₂' : Hom a' c)
    (j : Hom a' a), j ≫ proj₁ = proj₁' → j ≫ proj₂ = proj₂' →
    j = (mediating_morphism proj₁' proj₂').val

structure ProductData {C : Type u} [Category C] (b c : C) where
  obj : C
  proj₁ : Hom obj b
  proj₂ : Hom obj c
  is_product : IsProduct proj₁ proj₂

/--
When we say a category has all products, we mean that there is some specific choice
of product strcuture for each pair of objects.
-/
class HasProducts (C : Type u)[Category C] where
  mkProduct : ∀ (c d : C), ProductData c d

def product_obj {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : C :=
  (hp.mkProduct b c).obj

/-- Notation for composition of morphisms in a category (diagrammatic order) -/
infixr:60 " × " => product_obj

def product_proj₁ {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : Hom (product_obj b c) b :=
  (hp.mkProduct b c).proj₁

def product_proj₂ {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : Hom (product_obj b c) c :=
  (hp.mkProduct b c).proj₂

/-- Notation for projection maps -/
notation "Pr₁" => product_proj₁
notation "Pr₂" => product_proj₂

def product_proof {C : Type u}[Category C] [hp : HasProducts C]
  (b c : C) : IsProduct (Pr₁ b c) (Pr₂ b c) :=
  (hp.mkProduct b c).is_product

def fork {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : Hom x (a × b) :=
  ((product_proof a b).mediating_morphism f g)

/-- Use algebra of programming notation ▵ for fork map to a product -/
infix:80 " ▵ " => fork

theorem fork_β  {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : (f ▵ g) ≫ Pr₁ a b = f ∧ (f ▵ g) ≫ Pr₂ a b = g := by
  simp [fork]
  exact ((product_proof a b).mediating_morphism f g).property

@[simp] theorem fork_β₁  {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : (f ▵ g) ≫ Pr₁ a b = f := by
  apply And.left
  apply fork_β f g

@[simp] theorem fork_β₂  {C : Type u}[Category C] [hp : HasProducts C] {x a b : C}
  (f : Hom x a) (g : Hom x b) : (f ▵ g) ≫ Pr₂ a b = g := by
  apply And.right
  apply fork_β f g

def product {C : Type u}[Category C] [hp : HasProducts C] {a b c d : C}
  (f : Hom a c) (g : Hom b d) : Hom (a × b) (c × d) :=
  let proj₁' := (product_proj₁ a b) ≫ f
  let proj₂' := (product_proj₂ a b) ≫ g
  ((product_proof c d).mediating_morphism proj₁' proj₂')

/-- Use algebra of programming notation □ for product map -/
infix:80 " □ " => product
