import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-! # Two homogeneous addition laws on the cubic `y²z = x³ + xz²`

Two bihomogeneous addition laws of bidegree `(2, 2)` for the curve of `CubicGroup.lean`.
`cubicLawZ` is exceptional exactly on the diagonal, `cubicLawY` exactly where the difference of
the two points is a nonzero `2`-torsion point. Together they cover every pair of points.
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Curves

variable {R : Type*} [CommRing R]

/-- A coordinate triple `[X:Y:Z]` that satisfies `Y²Z = X³ + XZ²`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1, the homogeneous Weierstrass
equation with `a₄ = 1`. -/
def IsCubicTriple (p : Fin 3 → R) : Prop :=
  p 1 ^ 2 * p 2 = p 0 ^ 3 + p 0 * p 2 ^ 2

example : IsCubicTriple (![0, 1, 0] : Fin 3 → ℤ) := by
  simp [IsCubicTriple]

/-- The addition law whose exceptional pairs are the diagonal.
Source: Bosma and Lenstra, *Complete systems of two addition laws for elliptic curves*,
J. Number Theory 53 (1995), the law attached to the line `Z = 0`. -/
def cubicLawZ (p q : Fin 3 → R) : Fin 3 → R :=
  ![
    -(p 0)^2*(q 2)^2 + 2*(p 0)*(p 1)*(q 1)*(q 2) + (p 0)*(q 1)^2*(p 2) + (q 0)^2*(p 2)^2
      - (q 0)*(p 1)^2*(q 2) - 2*(q 0)*(p 1)*(q 1)*(p 2),
    -3*(p 0)^2*(q 0)*(q 1) + 3*(p 0)*(q 0)^2*(p 1) + (p 0)*(p 1)*(q 2)^2
      - 2*(p 0)*(q 1)*(p 2)*(q 2) + 2*(q 0)*(p 1)*(p 2)*(q 2) - (q 0)*(q 1)*(p 2)^2
      - (p 1)^2*(q 1)*(q 2) + (p 1)*(q 1)^2*(p 2),
    3*(p 0)^2*(q 0)*(q 2) - 3*(p 0)*(q 0)^2*(p 2) + (p 0)*(p 2)*(q 2)^2 - (q 0)*(p 2)^2*(q 2)
      - (p 1)^2*(q 2)^2 + (q 1)^2*(p 2)^2]

example : cubicLawZ (![0, 1, 0] : Fin 3 → ℤ) ![0, 0, 1] = ![0, 0, -1] := by
  ext i; fin_cases i <;> simp [cubicLawZ]

/-- The addition law whose exceptional pairs differ by a nonzero `2`-torsion point.
Source: Bosma and Lenstra, *Complete systems of two addition laws for elliptic curves*,
J. Number Theory 53 (1995), the law attached to the line `Y = 0`. -/
def cubicLawY (p q : Fin 3 → R) : Fin 3 → R :=
  ![
    -(p 0)^2*(q 1)*(q 2) - 2*(p 0)*(q 0)*(p 1)*(q 2) - 2*(p 0)*(q 0)*(q 1)*(p 2)
      + (p 0)*(p 1)*(q 1)^2 - (q 0)^2*(p 1)*(p 2) + (q 0)*(p 1)^2*(q 1) + (p 1)*(p 2)*(q 2)^2
      + (q 1)*(p 2)^2*(q 2),
    3*(p 0)^2*(q 0)^2 - (p 0)^2*(q 2)^2 - 4*(p 0)*(q 0)*(p 2)*(q 2) - (q 0)^2*(p 2)^2
      + (p 1)^2*(q 1)^2 - (p 2)^2*(q 2)^2,
    3*(p 0)^2*(q 0)*(q 1) + 3*(p 0)*(q 0)^2*(p 1) + (p 0)*(p 1)*(q 2)^2
      + 2*(p 0)*(q 1)*(p 2)*(q 2) + 2*(q 0)*(p 1)*(p 2)*(q 2) + (q 0)*(q 1)*(p 2)^2
      + (p 1)^2*(q 1)*(q 2) + (p 1)*(q 1)^2*(p 2)]

example : cubicLawY (![0, 1, 0] : Fin 3 → ℤ) ![0, 1, 0] = ![0, 1, 0] := by
  ext i; fin_cases i <;> simp [cubicLawY]

theorem cubicLawZ_isCubicTriple {p q : Fin 3 → R} (hp : IsCubicTriple p)
    (hq : IsCubicTriple q) : IsCubicTriple (cubicLawZ p q) := by
  unfold IsCubicTriple at hp hq ⊢
  simp only [cubicLawZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (
      -27*(p 0)^3*(q 0)^3*(q 1)^2*(q 2) - 9*(p 0)^3*(q 0)^2*(q 2)^4 - (p 0)^3*(q 2)^6
        + 54*(p 0)^2*(q 0)^4*(p 1)*(q 1)*(q 2) + 27*(p 0)^2*(q 0)^4*(q 1)^2*(p 2)
        + 18*(p 0)^2*(q 0)^3*(p 2)*(q 2)^3 + 36*(p 0)^2*(q 0)^2*(p 1)*(q 1)*(q 2)^3
        - 36*(p 0)^2*(q 0)^2*(q 1)^2*(p 2)*(q 2)^2 - 6*(p 0)^2*(q 0)*(p 2)*(q 2)^5
        + 6*(p 0)^2*(p 1)*(q 1)*(q 2)^5 + 3*(p 0)^2*(q 1)^2*(p 2)*(q 2)^4
        - 27*(p 0)*(q 0)^5*(p 1)^2*(q 2) - 54*(p 0)*(q 0)^5*(p 1)*(q 1)*(p 2)
        - 27*(p 0)*(q 0)^3*(p 1)^2*(q 2)^3 + 18*(p 0)*(q 0)^3*(p 1)*(q 1)*(p 2)*(q 2)^2
        + 36*(p 0)*(q 0)^3*(q 1)^2*(p 2)^2*(q 2) - 9*(p 0)*(q 0)^2*(p 1)^2*(q 1)^2*(q 2)^2
        + 18*(p 0)*(q 0)^2*(p 1)*(q 1)^3*(p 2)*(q 2) - 9*(p 0)*(q 0)^2*(q 1)^4*(p 2)^2
        + 24*(p 0)*(q 0)^2*(p 2)^2*(q 2)^4 + 24*(p 0)*(q 0)*(p 1)*(q 1)*(p 2)*(q 2)^4
        - 24*(p 0)*(q 0)*(q 1)^2*(p 2)^2*(q 2)^3 - 12*(p 0)*(p 1)^2*(q 1)^2*(q 2)^4
        - 12*(p 0)*(p 1)*(q 1)^3*(p 2)*(q 2)^3 - 3*(p 0)*(q 1)^4*(p 2)^2*(q 2)^2
        + 27*(q 0)^6*(p 1)^2*(p 2) - 18*(q 0)^5*(p 2)^3*(q 2) - 9*(q 0)^4*(p 1)^2*(p 2)*(q 2)^2
        - 72*(q 0)^4*(p 1)*(q 1)*(p 2)^2*(q 2) - 27*(q 0)^3*(p 1)^2*(q 1)^2*(p 2)*(q 2)
        - 18*(q 0)^3*(p 2)^3*(q 2)^3 - 36*(q 0)^2*(p 1)^2*(p 2)*(q 2)^4
        - 48*(q 0)^2*(p 1)*(q 1)*(p 2)^2*(q 2)^3 + 30*(q 0)^2*(q 1)^2*(p 2)^3*(q 2)^2
        + 12*(q 0)*(p 1)^2*(q 1)^2*(p 2)*(q 2)^3 + 48*(q 0)*(p 1)*(q 1)^3*(p 2)^2*(q 2)^2
        - 6*(q 0)*(q 1)^4*(p 2)^3*(q 2) + 8*(q 0)*(p 2)^3*(q 2)^5 + 8*(p 1)^3*(q 1)^3*(q 2)^3
        + 12*(p 1)^2*(q 1)^4*(p 2)*(q 2)^2 + 6*(p 1)*(q 1)^5*(p 2)^2*(q 2) + (q 1)^6*(p 2)^3
        - 8*(q 1)^2*(p 2)^3*(q 2)^4) * hp + (
      9*(p 0)^2*(q 0)^3*(p 2)^4 + 63*(p 0)^2*(q 0)^2*(p 1)^2*(p 2)^2*(q 2)
        + 18*(p 0)^2*(q 0)^2*(p 1)*(q 1)*(p 2)^3 + 9*(p 0)^2*(q 0)*(p 1)^4*(q 2)^2
        + 36*(p 0)^2*(q 0)*(p 1)^3*(q 1)*(p 2)*(q 2) + 36*(p 0)^2*(q 0)*(p 1)^2*(q 1)^2*(p 2)^2
        - 24*(p 0)^2*(q 0)*(p 2)^4*(q 2)^2 - 12*(p 0)^2*(p 1)^2*(p 2)^2*(q 2)^3
        - 24*(p 0)^2*(p 1)*(q 1)*(p 2)^3*(q 2)^2 - 27*(p 0)*(q 0)^3*(p 1)^2*(p 2)^3
        - 27*(p 0)*(q 0)^2*(p 1)^4*(p 2)*(q 2) - 54*(p 0)*(q 0)^2*(p 1)^3*(q 1)*(p 2)^2
        + 24*(p 0)*(q 0)^2*(p 2)^5*(q 2) + 60*(p 0)*(q 0)*(p 1)^2*(p 2)^3*(q 2)^2
        + 48*(p 0)*(q 0)*(p 1)*(q 1)*(p 2)^4*(q 2) + 6*(p 0)*(p 1)^4*(p 2)*(q 2)^3
        + 24*(p 0)*(p 1)^3*(q 1)*(p 2)^2*(q 2)^2 + 24*(p 0)*(p 1)^2*(q 1)^2*(p 2)^3*(q 2)
        - 8*(p 0)*(p 2)^5*(q 2)^3 + 27*(q 0)^3*(p 1)^4*(p 2)^2 + (q 0)^3*(p 2)^6
        - 21*(q 0)^2*(p 1)^2*(p 2)^4*(q 2) - 6*(q 0)^2*(p 1)*(q 1)*(p 2)^5
        - 33*(q 0)*(p 1)^4*(p 2)^2*(q 2)^2 - 60*(q 0)*(p 1)^3*(q 1)*(p 2)^3*(q 2)
        + 12*(q 0)*(p 1)^2*(q 1)^2*(p 2)^4 - (p 1)^6*(q 2)^3 - 6*(p 1)^5*(q 1)*(p 2)*(q 2)^2
        - 12*(p 1)^4*(q 1)^2*(p 2)^2*(q 2) - 8*(p 1)^3*(q 1)^3*(p 2)^3 + 8*(p 1)^2*(p 2)^4*(q 2)^3) * hq

theorem cubicLawY_isCubicTriple {p q : Fin 3 → R} (hp : IsCubicTriple p)
    (hq : IsCubicTriple q) : IsCubicTriple (cubicLawY p q) := by
  unfold IsCubicTriple at hp hq ⊢
  simp only [cubicLawY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (
      -27*(p 0)^3*(q 0)^5*(q 1) + 18*(p 0)^3*(q 0)^3*(q 1)*(q 2)^2
        - 9*(p 0)^3*(q 0)^2*(q 1)^3*(q 2) - 3*(p 0)^3*(q 0)*(q 1)*(q 2)^4
        - (p 0)^3*(q 1)^3*(q 2)^3 - 27*(p 0)^2*(q 0)^6*(p 1) + 9*(p 0)^2*(q 0)^4*(p 1)*(q 2)^2
        + 54*(p 0)^2*(q 0)^4*(q 1)*(p 2)*(q 2) - 36*(p 0)^2*(q 0)^3*(p 1)*(q 1)^2*(q 2)
        - 18*(p 0)^2*(q 0)^3*(q 1)^3*(p 2) + 9*(p 0)^2*(q 0)^2*(p 1)*(q 1)^4
        + 3*(p 0)^2*(q 0)^2*(p 1)*(q 2)^4 - 12*(p 0)^2*(q 0)^2*(q 1)*(p 2)*(q 2)^3
        - 12*(p 0)^2*(q 0)*(p 1)*(q 1)^2*(q 2)^3 - 18*(p 0)^2*(q 0)*(q 1)^3*(p 2)*(q 2)^2
        + 3*(p 0)^2*(p 1)*(q 1)^4*(q 2)^2 - (p 0)^2*(p 1)*(q 2)^6 - 2*(p 0)^2*(q 1)*(p 2)*(q 2)^5
        + 54*(p 0)*(q 0)^5*(p 1)*(p 2)*(q 2) + 36*(p 0)*(q 0)^5*(q 1)*(p 2)^2
        - 54*(p 0)*(q 0)^4*(p 1)^2*(q 1)*(q 2) - 54*(p 0)*(q 0)^4*(p 1)*(q 1)^2*(p 2)
        + 9*(p 0)*(q 0)^3*(p 1)^2*(q 1)^3 + 12*(p 0)*(q 0)^3*(p 1)*(p 2)*(q 2)^3
        - 24*(p 0)*(q 0)^2*(p 1)^2*(q 1)*(q 2)^3 - 72*(p 0)*(q 0)^2*(p 1)*(q 1)^2*(p 2)*(q 2)^2
        - 24*(p 0)*(q 0)^2*(q 1)^3*(p 2)^2*(q 2) + 21*(p 0)*(q 0)*(p 1)^2*(q 1)^3*(q 2)^2
        + 18*(p 0)*(q 0)*(p 1)*(q 1)^4*(p 2)*(q 2) - 10*(p 0)*(q 0)*(p 1)*(p 2)*(q 2)^5
        - 20*(p 0)*(q 0)*(q 1)*(p 2)^2*(q 2)^4 - 3*(p 0)*(p 1)^2*(q 1)^5*(q 2)
        - 2*(p 0)*(p 1)^2*(q 1)*(q 2)^5 - 2*(p 0)*(p 1)*(q 1)^2*(p 2)*(q 2)^4
        + 45*(q 0)^6*(p 1)*(p 2)^2 - 18*(q 0)^5*(p 1)^3*(q 2) - 63*(q 0)^5*(p 1)^2*(q 1)*(p 2)
        + 9*(q 0)^4*(p 1)^3*(q 1)^2 + 9*(q 0)^4*(p 1)*(p 2)^2*(q 2)^2
        - 42*(q 0)^4*(q 1)*(p 2)^3*(q 2) - 20*(q 0)^3*(p 1)^3*(q 2)^3
        - 54*(q 0)^3*(p 1)^2*(q 1)*(p 2)*(q 2)^2 - 36*(q 0)^3*(p 1)*(q 1)^2*(p 2)^2*(q 2)
        - 2*(q 0)^3*(q 1)^3*(p 2)^3 + 18*(q 0)^2*(p 1)^3*(q 1)^2*(q 2)^2
        + 51*(q 0)^2*(p 1)^2*(q 1)^3*(p 2)*(q 2) - 3*(q 0)^2*(p 1)*(q 1)^4*(p 2)^2
        - 37*(q 0)^2*(p 1)*(p 2)^2*(q 2)^4 - 44*(q 0)^2*(q 1)*(p 2)^3*(q 2)^3
        - 6*(q 0)*(p 1)^3*(q 1)^4*(q 2) - 2*(q 0)*(p 1)^3*(q 2)^5
        - 7*(q 0)*(p 1)^2*(q 1)*(p 2)*(q 2)^4 + 20*(q 0)*(p 1)*(q 1)^2*(p 2)^2*(q 2)^3
        + 30*(q 0)*(q 1)^3*(p 2)^3*(q 2)^2 + (p 1)^3*(q 1)^6 + (p 1)^3*(q 1)^2*(q 2)^4
        - 5*(p 1)^2*(q 1)^3*(p 2)*(q 2)^3 - 9*(p 1)*(q 1)^4*(p 2)^2*(q 2)^2
        - (p 1)*(p 2)^2*(q 2)^6 - 2*(q 1)*(p 2)^3*(q 2)^5) * hp + (
      -36*(p 0)^2*(q 0)^3*(p 1)^3*(p 2) + 9*(p 0)^2*(q 0)^2*(p 1)^4*(q 1)
        - 66*(p 0)^2*(q 0)^2*(p 1)*(p 2)^3*(q 2) - 33*(p 0)^2*(q 0)^2*(q 1)*(p 2)^4
        + 12*(p 0)^2*(q 0)*(p 1)^3*(p 2)*(q 2)^2 + 36*(p 0)^2*(q 0)*(p 1)^2*(q 1)*(p 2)^2*(q 2)
        + 30*(p 0)^2*(q 0)*(p 1)*(q 1)^2*(p 2)^3 - 3*(p 0)^2*(p 1)^4*(q 1)*(q 2)^2
        - 12*(p 0)^2*(p 1)^3*(q 1)^2*(p 2)*(q 2) - 9*(p 0)^2*(p 1)^2*(q 1)^3*(p 2)^2
        - 2*(p 0)^2*(p 1)*(p 2)^3*(q 2)^3 - (p 0)^2*(q 1)*(p 2)^4*(q 2)^2
        - 48*(p 0)*(q 0)^3*(p 1)*(p 2)^4 + 54*(p 0)*(q 0)^2*(p 1)^3*(p 2)^2*(q 2)
        + 87*(p 0)*(q 0)^2*(p 1)^2*(q 1)*(p 2)^3 - 36*(p 0)*(q 0)*(p 1)^4*(q 1)*(p 2)*(q 2)
        - 42*(p 0)*(q 0)*(p 1)^3*(q 1)^2*(p 2)^2 + 16*(p 0)*(q 0)*(p 1)*(p 2)^4*(q 2)^2
        + 32*(p 0)*(q 0)*(q 1)*(p 2)^5*(q 2) + 3*(p 0)*(p 1)^4*(q 1)^3*(p 2)
        - 10*(p 0)*(p 1)^3*(p 2)^2*(q 2)^3 - 25*(p 0)*(p 1)^2*(q 1)*(p 2)^3*(q 2)^2
        - 16*(p 0)*(p 1)*(q 1)^2*(p 2)^4*(q 2) + 44*(q 0)^3*(p 1)^3*(p 2)^3
        - 18*(q 0)^2*(p 1)^5*(p 2)*(q 2) - 60*(q 0)^2*(p 1)^4*(q 1)*(p 2)^2
        - 2*(q 0)^2*(p 1)*(p 2)^5*(q 2) - (q 0)^2*(q 1)*(p 2)^6 + 6*(q 0)*(p 1)^5*(q 1)^2*(p 2)
        - 36*(q 0)*(p 1)^3*(p 2)^3*(q 2)^2 - 44*(q 0)*(p 1)^2*(q 1)*(p 2)^4*(q 2)
        - 2*(q 0)*(p 1)*(q 1)^2*(p 2)^5 + (p 1)^6*(q 1)^3 - 2*(p 1)^5*(p 2)*(q 2)^3
        + 4*(p 1)^3*(q 1)^2*(p 2)^3*(q 2) - (p 1)^2*(q 1)^3*(p 2)^4 - 2*(p 1)*(p 2)^5*(q 2)^3
        - (q 1)*(p 2)^6*(q 2)^2) * hq

theorem cubicLawZ_smul (c d : R) (p q : Fin 3 → R) :
    cubicLawZ (fun k ↦ c * p k) (fun k ↦ d * q k) = fun k ↦ c ^ 2 * d ^ 2 * cubicLawZ p q k := by
  funext k
  fin_cases k <;> simp [cubicLawZ] <;> ring

theorem cubicLawY_smul (c d : R) (p q : Fin 3 → R) :
    cubicLawY (fun k ↦ c * p k) (fun k ↦ d * q k) = fun k ↦ c ^ 2 * d ^ 2 * cubicLawY p q k := by
  funext k
  fin_cases k <;> simp [cubicLawY] <;> ring

theorem map_cubicLawZ {S : Type*} [CommRing S] (f : R →+* S) (p q : Fin 3 → R) (k : Fin 3) :
    f (cubicLawZ p q k) = cubicLawZ (fun i ↦ f (p i)) (fun i ↦ f (q i)) k := by
  fin_cases k <;> simp [cubicLawZ, map_ofNat]

theorem map_cubicLawY {S : Type*} [CommRing S] (f : R →+* S) (p q : Fin 3 → R) (k : Fin 3) :
    f (cubicLawY p q k) = cubicLawY (fun i ↦ f (p i)) (fun i ↦ f (q i)) k := by
  fin_cases k <;> simp [cubicLawY, map_ofNat]

end HodgeLean.Foundations.Curves
