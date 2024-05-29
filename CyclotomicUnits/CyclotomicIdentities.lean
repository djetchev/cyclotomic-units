import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.RatFunc
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.RingTheory.RootsOfUnity.Basic

namespace CyclotomicUnits.CyclotomicIdentities

open BigOperators Polynomial

noncomputable section

universe u

variable {p n k b m : ℕ}
variable (hp : Nat.Prime p) (hn : n > 0) (hk : k > 0) (hkn : k < n)
variable [Field K] [Algebra ℚ K]
variable (ζpn : K) (ζpk : K) (ζpnmk : K)
variable (hζpn : IsPrimitiveRoot ζpn (p^n)) (hζpk : IsPrimitiveRoot ζpk (p^k))
variable (hζpnk : ζpn^(p^(n-k)) = ζpk)
variable (hζpnmk : ζpn^(p^k) = ζpnmk)
variable (f : ℕ → ℕ)

variable (ζm : K)
variable (hζm : IsPrimitiveRoot ζm m)

variable {R : Type*} [CommRing R] [IsDomain R]

lemma hζ_pow {a : ℕ} : (ζm^a)^m = 1 :=
  by simp [←pow_mul, mul_comm, pow_mul, hζm.pow_eq_one]

lemma dist_pows_of_prim_root {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
  ζm ^ i ≠ ζm ^ j := by
  intro h
  have h_pow : ζm ^ (i - j) = 1 := by
    simp [←pow_sub ζm (le_of_lt (lt_of_le_of_ne (le_of_lt hi) (Ne.symm hij))), h]


lemma factor_xm_sub_1 {m : ℕ} {ζm : K} (hζm : IsPrimitiveRoot ζm m) :
  X^m - 1 = ∏ a in (Finset.range m), (X - C ζm^a) := by
  sorry

lemma lin_term_rewrite {a : ℕ} (ha : a ≤ m) : C 1 - C ζm^a * X = -C ζm^a * (X - C ζm^(m-a)) :=
  have hζa_inv {a : ℕ} (ha : a ≤ m) : C ζm^a * C ζm^(m-a) = C 1 :=
    by simp only [←C_mul, ←pow_add, Nat.add_sub_cancel' ha, ←C_pow, hζm.pow_eq_one]
  calc
    C 1 - C ζm^a * X = C ζm^a * C ζm^(m-a) - C ζm^a * X       := by simp [←hζa_inv ha]
    _ = C ζm^a * C ζm^(m-a) - C ζm^a * X                      := by simp [←right_distrib]
    _ = -C ζm^a * (X - C ζm^(m-a))                            := by ring

@[simp]
lemma factor_1_sub_xm {m : ℕ} {ζm : K} (hζm : IsPrimitiveRoot ζm m) :
  ∏ a in (Finset.range m), (C 1 - C ζm^a * X) = C 1 - X^m :=
  calc
    ∏ a in (Finset.range m), (C 1 - C ζm^a * X) = ∏ a in (Finset.range m), (-C ζm^a * (X - C ζm^(m-a)))   := by rw [lin_term_rewrite]
    _ = ∏ a in (Finset.range m), -C ζm^a * ∏ a in (Finset.range m), (X - C ζm^(m-a))                      := by rw [Finset.prod_mul_distrib]
    _ = ∏ a in (Finset.range m), -C ζm^a * ∏ a in (Finset.range m), (X - C ζm^a)                          := by rw [Finset.prod_range_reflect]
    _ = ∏ a in (Finset.range m), -C ζm^a * (X - C 1)                                                      := by rw [factor_1_sub_x]

@[simp]
lemma product_rewrite :
  ∏ a in (Finset.range (p^n)).filter (λ a => a % p^k == b), (1 - ζpn ^ a) = ∏ m in (Finset.range ((p^n - b) / p^k)), (1 - ζpn ^ (p^k * m + b)) :=
  by sorry

theorem product_cyclotomic_units_mod_range (hp : p > 0) (hn : n > 0)  (b : ℕ) (hb : b < p^k) :
  ∏ a in (Finset.range (p^n)).filter (λ a => a % p^k == b), (1 - ζpn ^ a) = 1 - ζpk ^ b := by
  simp only [product_rewrite, pow_add, pow_mul, hζpnmk]
