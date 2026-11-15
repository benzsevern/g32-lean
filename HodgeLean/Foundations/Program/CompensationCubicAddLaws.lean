import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-! # Homogeneous addition laws on the CM cubic -/
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.CompensationCubic
variable {R : Type*} [CommRing R]

/-- A homogeneous addition law for the CM cubic.
Source: Bosma and Lenstra, J. Number Theory 53 (1995), §2. -/
def cubicLawZ (p q : Fin 3 → R) : Fin 3 → R :=
  ![2*(p 0)*(p 1)*(q 1)*(q 2) + (p 0)*(q 1) ^ 2*(p 2) - 3*(p 0)*(p 2)*(q 2) ^ 2 - (q 0)*(p 1) ^ 2*(q 2) - 2*(q 0)*(p 1)*(q 1)*(p 2) + 3*(q 0)*(p 2) ^ 2*(q 2),
    -3*(p 0) ^ 2*(q 0)*(q 1) + 3*(p 0)*(q 0) ^ 2*(p 1) - (p 1) ^ 2*(q 1)*(q 2) + (p 1)*(q 1) ^ 2*(p 2) + 3*(p 1)*(p 2)*(q 2) ^ 2 - 3*(q 1)*(p 2) ^ 2*(q 2),
    3*(p 0) ^ 2*(q 0)*(q 2) - 3*(p 0)*(q 0) ^ 2*(p 2) - (p 1) ^ 2*(q 2) ^ 2 + (q 1) ^ 2*(p 2) ^ 2]

theorem cubicLawZ_isCubicTriple {p q : Fin 3 → R}
    (hp : p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3)
    (hq : q 1 ^ 2 * q 2 = q 0 ^ 3 + q 2 ^ 3) :
    cubicLawZ p q 1 ^ 2 * cubicLawZ p q 2 =
      cubicLawZ p q 0 ^ 3 + cubicLawZ p q 2 ^ 3 := by
  simp only [cubicLawZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-27*(p 0) ^ 3*(q 0) ^ 6 + 12*(p 0) ^ 3*(q 0) ^ 3*(q 1) ^ 2*(q 2) - 9*(p 0) ^ 3*(q 0) ^ 3*(q 2) ^ 3 - 12*(p 0) ^ 3*(q 1) ^ 4*(q 2) ^ 2 + 21*(p 0) ^ 3*(q 1) ^ 2*(q 2) ^ 4 - 9*(p 0) ^ 3*(q 2) ^ 6 + 18*(p 0) ^ 2*(q 0) ^ 4*(p 1)*(q 1)*(q 2) - 9*(p 0) ^ 2*(q 0) ^ 4*(q 1) ^ 2*(p 2) - 27*(p 0) ^ 2*(q 0) ^ 4*(p 2)*(q 2) ^ 2 + 36*(p 0) ^ 2*(q 0)*(p 1)*(q 1) ^ 3*(q 2) ^ 2 - 36*(p 0) ^ 2*(q 0)*(p 1)*(q 1)*(q 2) ^ 4 + 36*(p 0) ^ 2*(q 0)*(q 1) ^ 4*(p 2)*(q 2) - 90*(p 0) ^ 2*(q 0)*(q 1) ^ 2*(p 2)*(q 2) ^ 3 + 54*(p 0) ^ 2*(q 0)*(p 2)*(q 2) ^ 5 - 36*(p 0)*(q 0) ^ 2*(p 1) ^ 2*(q 1) ^ 2*(q 2) ^ 2 - 36*(p 0)*(q 0) ^ 2*(p 1)*(q 1) ^ 3*(p 2)*(q 2) + 108*(p 0)*(q 0) ^ 2*(p 1)*(q 1)*(p 2)*(q 2) ^ 3 - 9*(p 0)*(q 0) ^ 2*(q 1) ^ 4*(p 2) ^ 2 + 54*(p 0)*(q 0) ^ 2*(q 1) ^ 2*(p 2) ^ 2*(q 2) ^ 2 - 81*(p 0)*(q 0) ^ 2*(p 2) ^ 2*(q 2) ^ 4 + 6*(q 0) ^ 3*(p 1) ^ 3*(q 1)*(q 2) ^ 2 + 12*(q 0) ^ 3*(p 1) ^ 2*(q 1) ^ 2*(p 2)*(q 2) - 9*(q 0) ^ 3*(p 1) ^ 2*(p 2)*(q 2) ^ 3 + 8*(q 0) ^ 3*(p 1)*(q 1) ^ 3*(p 2) ^ 2 - 30*(q 0) ^ 3*(p 1)*(q 1)*(p 2) ^ 2*(q 2) ^ 2 - 24*(q 0) ^ 3*(q 1) ^ 2*(p 2) ^ 3*(q 2) + 18*(q 0) ^ 3*(p 2) ^ 3*(q 2) ^ 3 + 2*(p 1) ^ 3*(q 1) ^ 3*(q 2) ^ 3 + 6*(p 1) ^ 3*(q 1)*(q 2) ^ 5 - 15*(p 1) ^ 2*(q 1) ^ 2*(p 2)*(q 2) ^ 4 - 9*(p 1) ^ 2*(p 2)*(q 2) ^ 6 - 2*(p 1)*(q 1) ^ 5*(p 2) ^ 2*(q 2) + 2*(p 1)*(q 1) ^ 3*(p 2) ^ 2*(q 2) ^ 3 + 24*(p 1)*(q 1)*(p 2) ^ 2*(q 2) ^ 5 + (q 1) ^ 6*(p 2) ^ 3 + 15*(q 1) ^ 4*(p 2) ^ 3*(q 2) ^ 2 - 15*(q 1) ^ 2*(p 2) ^ 3*(q 2) ^ 4 - 9*(p 2) ^ 3*(q 2) ^ 6) * hp + (
    27*(p 0) ^ 6*(q 0) ^ 3 - 12*(p 0) ^ 6*(q 1) ^ 2*(q 2) + 9*(p 0) ^ 6*(q 2) ^ 3 + 36*(p 0) ^ 5*(q 0)*(p 1)*(q 1)*(q 2) + 36*(p 0) ^ 5*(q 0)*(q 1) ^ 2*(p 2) - 54*(p 0) ^ 5*(q 0)*(p 2)*(q 2) ^ 2 - 27*(p 0) ^ 4*(q 0) ^ 2*(p 1) ^ 2*(q 2) - 54*(p 0) ^ 4*(q 0) ^ 2*(p 1)*(q 1)*(p 2) + 81*(p 0) ^ 4*(q 0) ^ 2*(p 2) ^ 2*(q 2) - 6*(p 0) ^ 3*(p 1) ^ 3*(q 1)*(q 2) ^ 2 - 8*(p 0) ^ 3*(p 1)*(q 1) ^ 3*(p 2) ^ 2 + 30*(p 0) ^ 3*(p 1)*(q 1)*(p 2) ^ 2*(q 2) ^ 2 + 12*(p 0) ^ 3*(q 1) ^ 2*(p 2) ^ 3*(q 2) - 9*(p 0) ^ 3*(p 2) ^ 3*(q 2) ^ 3 + 9*(p 0) ^ 2*(q 0)*(p 1) ^ 4*(q 2) ^ 2 - 72*(p 0) ^ 2*(q 0)*(p 1)*(q 1)*(p 2) ^ 3*(q 2) + 36*(p 0) ^ 2*(q 0)*(q 1) ^ 2*(p 2) ^ 4 + 27*(p 0) ^ 2*(q 0)*(p 2) ^ 4*(q 2) ^ 2 - (p 1) ^ 6*(q 2) ^ 3 - 8*(p 1)*(q 1) ^ 3*(p 2) ^ 5 - 24*(p 1)*(q 1)*(p 2) ^ 5*(q 2) ^ 2 + 24*(q 1) ^ 2*(p 2) ^ 6*(q 2) + 9*(p 2) ^ 6*(q 2) ^ 3) * hq

/-- A homogeneous addition law for the CM cubic.
Source: Bosma and Lenstra, J. Number Theory 53 (1995), §2. -/
def cubicLawY (p q : Fin 3 → R) : Fin 3 → R :=
  ![(p 0)*(p 1)*(q 1) ^ 2 - 3*(p 0)*(p 1)*(q 2) ^ 2 - 6*(p 0)*(q 1)*(p 2)*(q 2) + (q 0)*(p 1) ^ 2*(q 1) - 6*(q 0)*(p 1)*(p 2)*(q 2) - 3*(q 0)*(q 1)*(p 2) ^ 2,
    9*(p 0) ^ 2*(q 0)*(q 2) + 9*(p 0)*(q 0) ^ 2*(p 2) + (p 1) ^ 2*(q 1) ^ 2 - 9*(p 2) ^ 2*(q 2) ^ 2,
    3*(p 0) ^ 2*(q 0)*(q 1) + 3*(p 0)*(q 0) ^ 2*(p 1) + (p 1) ^ 2*(q 1)*(q 2) + (p 1)*(q 1) ^ 2*(p 2) + 3*(p 1)*(p 2)*(q 2) ^ 2 + 3*(q 1)*(p 2) ^ 2*(q 2)]

theorem cubicLawY_isCubicTriple {p q : Fin 3 → R}
    (hp : p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3)
    (hq : q 1 ^ 2 * q 2 = q 0 ^ 3 + q 2 ^ 3) :
    cubicLawY p q 1 ^ 2 * cubicLawY p q 2 =
      cubicLawY p q 0 ^ 3 + cubicLawY p q 2 ^ 3 := by
  simp only [cubicLawY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (9*(p 0) ^ 3*(q 0) ^ 3*(q 1) ^ 3 - 108*(p 0) ^ 3*(q 0) ^ 3*(q 1)*(q 2) ^ 2 + 18*(p 0) ^ 3*(q 1) ^ 5*(q 2) - 153*(p 0) ^ 3*(q 1) ^ 3*(q 2) ^ 3 + 135*(p 0) ^ 3*(q 1)*(q 2) ^ 5 + 27*(p 0) ^ 2*(q 0) ^ 4*(p 1)*(q 1) ^ 2 - 81*(p 0) ^ 2*(q 0) ^ 4*(p 1)*(q 2) ^ 2 + 54*(p 0) ^ 2*(q 0)*(p 1)*(q 1) ^ 4*(q 2) - 216*(p 0) ^ 2*(q 0)*(p 1)*(q 1) ^ 2*(q 2) ^ 3 + 162*(p 0) ^ 2*(q 0)*(p 1)*(q 2) ^ 5 - 486*(p 0) ^ 2*(q 0)*(q 1) ^ 3*(p 2)*(q 2) ^ 2 + 486*(p 0) ^ 2*(q 0)*(q 1)*(p 2)*(q 2) ^ 4 + 54*(p 0)*(q 0) ^ 2*(p 1) ^ 2*(q 1) ^ 3*(q 2) - 162*(p 0)*(q 0) ^ 2*(p 1) ^ 2*(q 1)*(q 2) ^ 3 + 27*(p 0)*(q 0) ^ 2*(p 1)*(q 1) ^ 4*(p 2) - 486*(p 0)*(q 0) ^ 2*(p 1)*(q 1) ^ 2*(p 2)*(q 2) ^ 2 + 243*(p 0)*(q 0) ^ 2*(p 1)*(p 2)*(q 2) ^ 4 - 162*(p 0)*(q 0) ^ 2*(q 1) ^ 3*(p 2) ^ 2*(q 2) + 486*(p 0)*(q 0) ^ 2*(q 1)*(p 2) ^ 2*(q 2) ^ 3 + 18*(q 0) ^ 3*(p 1) ^ 3*(q 1) ^ 2*(q 2) + 9*(q 0) ^ 3*(p 1) ^ 2*(q 1) ^ 3*(p 2) - 108*(q 0) ^ 3*(p 1) ^ 2*(q 1)*(p 2)*(q 2) ^ 2 - 90*(q 0) ^ 3*(p 1)*(q 1) ^ 2*(p 2) ^ 2*(q 2) + 216*(q 0) ^ 3*(p 1)*(p 2) ^ 2*(q 2) ^ 3 - 18*(q 0) ^ 3*(q 1) ^ 3*(p 2) ^ 3 + 216*(q 0) ^ 3*(q 1)*(p 2) ^ 3*(q 2) ^ 2 + (p 1) ^ 3*(q 1) ^ 6 - 9*(p 1) ^ 3*(q 1) ^ 2*(q 2) ^ 4 - 45*(p 1) ^ 2*(q 1) ^ 3*(p 2)*(q 2) ^ 3 - 27*(p 1) ^ 2*(q 1)*(p 2)*(q 2) ^ 5 - 45*(p 1)*(q 1) ^ 4*(p 2) ^ 2*(q 2) ^ 2 - 144*(p 1)*(q 1) ^ 2*(p 2) ^ 2*(q 2) ^ 4 - 27*(p 1)*(p 2) ^ 2*(q 2) ^ 6 - 9*(q 1) ^ 5*(p 2) ^ 3*(q 2) - 180*(q 1) ^ 3*(p 2) ^ 3*(q 2) ^ 3 - 27*(q 1)*(p 2) ^ 3*(q 2) ^ 5) * hp + (
    18*(p 0) ^ 6*(q 1) ^ 3 - 135*(p 0) ^ 6*(q 1)*(q 2) ^ 2 + 54*(p 0) ^ 5*(q 0)*(p 1)*(q 1) ^ 2 - 162*(p 0) ^ 5*(q 0)*(p 1)*(q 2) ^ 2 - 486*(p 0) ^ 5*(q 0)*(q 1)*(p 2)*(q 2) + 81*(p 0) ^ 4*(q 0) ^ 2*(p 1) ^ 2*(q 1) - 486*(p 0) ^ 4*(q 0) ^ 2*(p 1)*(p 2)*(q 2) - 243*(p 0) ^ 4*(q 0) ^ 2*(q 1)*(p 2) ^ 2 + 27*(p 0) ^ 3*(q 0) ^ 3*(p 1) ^ 3 - 243*(p 0) ^ 3*(q 0) ^ 3*(p 1)*(p 2) ^ 2 + 9*(p 0) ^ 3*(p 1) ^ 3*(q 1) ^ 2*(q 2) - 27*(p 0) ^ 3*(p 1) ^ 3*(q 2) ^ 3 - 153*(p 0) ^ 3*(p 1)*(q 1) ^ 2*(p 2) ^ 2*(q 2) + 27*(p 0) ^ 3*(p 1)*(p 2) ^ 2*(q 2) ^ 3 + 9*(p 0) ^ 3*(q 1) ^ 3*(p 2) ^ 3 - 108*(p 0) ^ 3*(q 1)*(p 2) ^ 3*(q 2) ^ 2 + 27*(p 0) ^ 2*(q 0)*(p 1) ^ 4*(q 1)*(q 2) - 108*(p 0) ^ 2*(q 0)*(p 1)*(q 1) ^ 2*(p 2) ^ 3 + 324*(p 0) ^ 2*(q 0)*(p 1)*(p 2) ^ 3*(q 2) ^ 2 - 243*(p 0) ^ 2*(q 0)*(q 1)*(p 2) ^ 4*(q 2) + (p 1) ^ 6*(q 1) ^ 3 - 72*(p 1)*(q 1) ^ 2*(p 2) ^ 5*(q 2) - 216*(p 1)*(p 2) ^ 5*(q 2) ^ 3 - 9*(q 1) ^ 3*(p 2) ^ 6 - 216*(q 1)*(p 2) ^ 6*(q 2) ^ 2) * hq

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

end HodgeLean.Foundations.Program.CompensationCubic
