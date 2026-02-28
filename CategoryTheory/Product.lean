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
open UniversalCone

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
    -- now need to prove HEq to show equality of morphisms
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


/--
This shows that having general limits of shape |2| = . . (ProductDiagram), means
a category has products (in the fully unfolded sense)
-/
def limits_of_product_diagram_to_product
 {C : Type u} [Category C] [Lim : HasLimitsOfDiagram ProductDiagram C] : HasProducts C := by
  refine {mkProduct := ?_}
  intro c d
  let associated_functor : Functor ProductDiagram C := product_hom.invFun ⟨c, d⟩
  have f_0 : associated_functor.F₀ {el := 0} = c := by
    simp [associated_functor, product_hom]
  have f_1 : associated_functor.F₀ {el := 1} = d := by
    simp [associated_functor, product_hom]
  let mk_cone (T : C) (pr'₁ : T ⇒ c) (pr'₂ : T ⇒ d) : Cone associated_functor := by
    refine {obj := T, C₀ := ?_, commutes := ?_}
    · intro ⟨i⟩
      match i with
      | 0 => exact pr'₁
      | 1 => exact pr'₂
    · intro n m eq
      subst eq
      match n with
      | ⟨0⟩ => simp [associated_functor, product_hom]
      | ⟨1⟩ => simp [associated_functor, product_hom]
  let universal_cone : UniversalCone associated_functor := Lim.mkLimit associated_functor
  let univ₁ := universal_cone.C₀ {el := 0}
  let univ₂ := universal_cone.C₀ {el := 1}
  refine {obj := ?_, proj₁ := ?_, proj₂ := ?_, is_product := ?_}
  · exact universal_cone.obj
  · exact univ₁
  · exact univ₂
  · refine {mediating_morphism := ?_, unique := ?_}
    -- first show that if we have the universal cone then we get a mediating
    -- morphism from it
    · intro T pr'₁ pr'₂
      let T_cone : Cone associated_functor := mk_cone T pr'₁ pr'₂
      let T_mediating := universal_cone.mediating T_cone
      refine {val := ?_, property := ?_}
      · exact T_mediating.val
      · let at_0 : pr'₁ = ↑T_mediating ≫ univ₁ := T_mediating.property ⟨0⟩
        let at_1 : pr'₂ = ↑T_mediating ≫ univ₂ := T_mediating.property ⟨1⟩
        exact ⟨by symm; exact at_0, by symm; exact at_1⟩
    -- now use uniqueness of the universal cone to show the mediating morphism is
    -- unique
    · intro T pr'₁ pr'₂ mediate' mediate_β₁ mediate_β₂
      let T_cone : Cone associated_functor := mk_cone T pr'₁ pr'₂
      have cone_mediate :
        ∀ (i : ProductDiagram) , T_cone.C₀ i = mediate' ≫ universal_cone.C₀ i := by
        intro i
        match i with
        | ⟨0⟩ =>
          simp [T_cone, mk_cone]
          exact mediate_β₁.symm
        | ⟨1⟩ =>
          simp [T_cone, mk_cone]
          exact mediate_β₂.symm
      apply universal_cone.univ T_cone mediate' cone_mediate



def product_to_limits_of_diagram
 {C : Type u} [Category C] [Prod : HasProducts C] : HasLimitsOfDiagram ProductDiagram C := by
  refine {mkLimit := ?_}
  intro F
  let c₀ : C := F.F₀ ⟨0⟩
  let c₁ : C := F.F₀ ⟨1⟩
  let prod := Prod.mkProduct c₀ c₁
  refine {obj := ?_, C₀ := ?_, mediating := ?_, commutes := ?_, univ :=?_}
  · exact prod.obj
  · intro i
    match i with
    | ⟨0⟩ => exact prod.proj₁
    | ⟨1⟩ => exact prod.proj₂
  · intro i j eq
    subst eq
    simp
  · intro cone_F
    let T : C := cone_F.obj
    let proj'₁ : Hom T c₀  := cone_F.C₀ ⟨0⟩
    let proj'₂ : Hom T c₁ := cone_F.C₀ ⟨1⟩
    let mediates := prod.is_product.mediating_morphism proj'₁ proj'₂
    refine {val := ?_, property := ?_}
    · exact mediates.val
    · intro i
      match i with
      | ⟨0⟩ =>
        rw [mediates.property.left]
      | ⟨1⟩ =>
        rw [mediates.property.right]
  · intro cone_F mediate_map cone_mediates
    let T : C := cone_F.obj
    let proj'₁ : Hom T c₀  := cone_F.C₀ ⟨0⟩
    let proj'₂ : Hom T c₁ := cone_F.C₀ ⟨1⟩
    let mediates := prod.is_product.mediating_morphism proj'₁ proj'₂
    apply prod.is_product.unique
    rw [cone_mediates ⟨0⟩]
    rw [cone_mediates ⟨1⟩]
