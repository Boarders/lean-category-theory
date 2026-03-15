import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.Group.Hom.Defs

universe v u

structure MagmaWithIdentity (M : Type u) where
  mul : M → M → M
  one : M
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a

@[simp]
lemma MagmaWithIdentity.one_mul_simp {M : Type u} (m : MagmaWithIdentity M) {a : M} :
    m.mul m.one a = a := m.one_mul a

@[simp]
lemma MagmaWithIdentity.mul_one_simp {M : Type u} (m : MagmaWithIdentity M) {a : M} :
    m.mul a m.one = a := m.mul_one a

theorem eckman_hilton {M : Type u} (M1 M2 : MagmaWithIdentity M)
    (interchange : ∀ {a b c d}, M1.mul (M2.mul a b) (M2.mul c d) = M2.mul (M1.mul a c) (M1.mul b d)) :
    M1.mul = M2.mul := by

  have ids_equal : M1.one = M2.one := by
    calc M1.one
      _ = M1.mul M1.one M1.one := (M1.one_mul M1.one).symm
      _ = M1.mul (M2.mul M2.one M1.one) (M2.mul M1.one M2.one) := by
            simp
      _ = M2.mul (M1.mul M2.one M1.one) (M1.mul M1.one M2.one) := interchange
      _ = M2.mul M2.one M2.one := by
        simp
      _ = M2.one := M2.one_mul M2.one
  have M1ab_M2ba a b : M1.mul a b = M2.mul b a :=
    calc M1.mul a b
    _ = M1.mul (M2.mul M2.one a) (M2.mul b M2.one) := by
          simp
    _ = M2.mul (M1.mul M2.one b) (M1.mul a M2.one) := interchange
    _ = M2.mul (M1.mul M1.one b) (M1.mul a M1.one) := by
          rw [ids_equal]
    _ = M2.mul b a := by
      simp
  have M2ba_M1ba a b : M2.mul b a = M1.mul b a :=
    calc M2.mul b a
    _ = M2.mul (M1.mul b M1.one) (M1.mul M1.one a) := by
      simp
    _ = M1.mul (M2.mul b M1.one) (M2.mul M1.one a) := interchange.symm
    _ = M1.mul (M2.mul b M2.one) (M2.mul M2.one a) := by
      rw [ids_equal]
    _ = M1.mul b a := by simp
  funext a b
  trans M1.mul b a
  · exact (M1ab_M2ba a b).trans (M2ba_M1ba a b)
  · exact M1ab_M2ba b a
