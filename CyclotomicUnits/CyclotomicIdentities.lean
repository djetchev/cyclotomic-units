import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace CyclotomicUnits.CyclotomicIdentities

open scoped BigOperators

variable {p n k b : ℕ}
variable (hp : Nat.Prime p) (hn : n > 0) (hk : k > 0) (hkn : k < n)
variable [Field K] [Algebra ℚ K]
variable (ζpn : K) (ζpk : K) (ζpnmk : K)
variable (hζpn : IsPrimitiveRoot ζpn (p^n)) (hζpk : IsPrimitiveRoot ζpk (p^k))
variable (hζpnk : ζpn^(p^(n-k)) = ζpk)
variable (hζpnmk : ζpn^(p^k) = ζpnmk)
variable (f : ℕ → ℕ)

lemma factor_xm_sub_1 {m : ℕ} {ζm : ℂ} (hζm : IsPrimitiveRoot ζm m) :
  x^m - 1 = ∏ a in (Finset.range m), (x - ζm^a) := by
  sorry

theorem product_cyclotomic_units :
  ∏ a in (Finset.range (p^n)).filter (λ a => a % p^k == b), (1 - ζpn ^ a) = 1 - ζpk ^ b := by
  sorry

end CyclotomicUnits.CyclotomicIdentities
