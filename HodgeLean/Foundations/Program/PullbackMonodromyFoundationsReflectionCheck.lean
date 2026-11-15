import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsReflectionData

set_option maxHeartbeats 400000

/-! # Kernel checks for the reflection class of `r₁` in G32

The form `b65t_H` is invariant under the integral generators, the orbit list is closed under
them and contains every standard basis vector, the listed conjugates have the stated words, and
for every orbit vector `c ≠ e_j` the rank-one matrix determined by `v = c - e_j` is either not
divisible by `σ(v)ᵀ H v` or equals that scalar times a listed conjugate.
HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Program

open HurwitzPrymRex_Zw

/-- Galois conjugation `ω ↦ ω²` on `ℤ[ω]`: `a + bω ↦ (a - b) - bω`.
Source: Ireland–Rosen, GTM 84, §1.4 (complex conjugation on `ℤ[ω]`). -/
def b65t_sig (x : HurwitzPrymRex_Zw) : HurwitzPrymRex_Zw := ⟨x.re - x.om, -x.om⟩

/-- The conjugate transpose over `ℤ[ω]`.
Source: the definition of the conjugate transpose. -/
def b65t_star (A : HurwitzPrymRex_Mat) : HurwitzPrymRex_Mat := fun i j ↦ b65t_sig (A j i)

/-- Matrix times vector over `ℤ[ω]`, written out as in `HurwitzPrymRex_mmul`.
Source: the definition of the matrix product. -/
def b65t_mv (A : HurwitzPrymRex_Mat) (v : Fin 4 → HurwitzPrymRex_Zw) : Fin 4 → HurwitzPrymRex_Zw :=
  fun i ↦ add (add (mul (A i 0) (v 0)) (mul (A i 1) (v 1)))
    (add (mul (A i 2) (v 2)) (mul (A i 3) (v 3)))

/-- Entrywise Boolean equality of vectors.
Source: the definition of vector equality. -/
def b65t_vbeq (u v : Fin 4 → HurwitzPrymRex_Zw) : Bool :=
  u 0 == v 0 && u 1 == v 1 && u 2 == v 2 && u 3 == v 3

/-- Membership in a list of vectors.
Source: `List.any`. -/
def b65t_vmem (v : Fin 4 → HurwitzPrymRex_Zw) (L : List (Fin 4 → HurwitzPrymRex_Zw)) : Bool :=
  L.any (b65t_vbeq v)

/-- The standard basis vector `e_j`.
Source: the definition of the standard basis. -/
def b65t_e (j : Fin 4) : Fin 4 → HurwitzPrymRex_Zw := fun i ↦ if i = j then z 1 0 else z 0 0

/-- The row vector `σ(v)ᵀ H`.
Source: the sesquilinear form of `b65t_H`. -/
def b65t_beta (v : Fin 4 → HurwitzPrymRex_Zw) : Fin 4 → HurwitzPrymRex_Zw :=
  fun k ↦ add (add (mul (b65t_sig (v 0)) (b65t_H 0 k)) (mul (b65t_sig (v 1)) (b65t_H 1 k)))
    (add (mul (b65t_sig (v 2)) (b65t_H 2 k)) (mul (b65t_sig (v 3)) (b65t_H 3 k)))

/-- The value `σ(v)ᵀ H v`.
Source: the sesquilinear form of `b65t_H`. -/
def b65t_hval (v : Fin 4 → HurwitzPrymRex_Zw) : HurwitzPrymRex_Zw :=
  add (add (mul (b65t_beta v 0) (v 0)) (mul (b65t_beta v 1) (v 1)))
    (add (mul (b65t_beta v 2) (v 2)) (mul (b65t_beta v 3) (v 3)))

/-- The matrix `h · 1 + (ω - 1) v (σ(v)ᵀ H)` with `h = σ(v)ᵀ H v`.
Source: the formula for a unitary reflection with root `v` and eigenvalue `ω`. -/
def b65t_R (v : Fin 4 → HurwitzPrymRex_Zw) : HurwitzPrymRex_Mat := fun i k ↦
  add (if i = k then b65t_hval v else z 0 0) (mul (z (-1) 1) (mul (v i) (b65t_beta v k)))

/-- Divisibility of `x` by `h` in `ℤ[ω]`, through the norm `h σ(h)`.
Source: Ireland–Rosen, GTM 84, §1.4. -/
def b65t_dvd (h x : HurwitzPrymRex_Zw) : Bool :=
  (mul x (b65t_sig h)).re % (mul h (b65t_sig h)).re == 0 &&
    (mul x (b65t_sig h)).om % (mul h (b65t_sig h)).re == 0

/-- Every entry of `A` is divisible by `h`.
Source: Ireland–Rosen, GTM 84, §1.4. -/
def b65t_allDvd (h : HurwitzPrymRex_Zw) (A : HurwitzPrymRex_Mat) : Bool :=
  (List.finRange 4).all fun i ↦ (List.finRange 4).all fun k ↦ b65t_dvd h (A i k)

/-- Scalar multiple of a matrix.
Source: the definition of scalar multiplication. -/
def b65t_smul (h : HurwitzPrymRex_Zw) (A : HurwitzPrymRex_Mat) : HurwitzPrymRex_Mat :=
  fun i k ↦ mul h (A i k)

/-- The check for one orbit vector `c` in column `j`.
Source: the formula for a unitary reflection with root `v` and eigenvalue `ω`. -/
def b65t_columnOk (j : Fin 4) (c : Fin 4 → HurwitzPrymRex_Zw) : Bool :=
  b65t_vbeq c (b65t_e j) ||
    (!(b65t_hval (fun i ↦ add (c i) (mul (z (-1) 0) (b65t_e j i))) == z 0 0) &&
      (!(b65t_allDvd (b65t_hval (fun i ↦ add (c i) (mul (z (-1) 0) (b65t_e j i))))
          (b65t_R (fun i ↦ add (c i) (mul (z (-1) 0) (b65t_e j i))))) ||
        b65t_class.any fun t ↦ HurwitzPrymRex_mbeq
          (b65t_R (fun i ↦ add (c i) (mul (z (-1) 0) (b65t_e j i))))
          (b65t_smul (b65t_hval (fun i ↦ add (c i) (mul (z (-1) 0) (b65t_e j i)))) t.1)))

/-- Integral matrix of a positive word, as `b65s_ew`.
Source: `HurwitzPrymRex_g32SOne`. -/
def b65t_ew (w : List (Fin 4)) : HurwitzPrymRex_Mat :=
  w.foldr (fun i M ↦ HurwitzPrymRex_mmul (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i) M)
    HurwitzPrymRex_mone

theorem b65t_H_invariant : ∀ i : Fin 4, HurwitzPrymRex_mbeq
    (HurwitzPrymRex_mmul (b65t_star (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i))
      (HurwitzPrymRex_mmul b65t_H (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i))) b65t_H = true := by
  decide +kernel

theorem b65t_orbit_closed : b65t_orbit.all (fun c ↦ (List.finRange 4).all fun i ↦
    b65t_vmem (b65t_mv (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i) c) b65t_orbit) = true := by
  decide +kernel

theorem b65t_basis_mem : ∀ j : Fin 4, b65t_vmem (b65t_e j) b65t_orbit = true := by
  decide +kernel

theorem b65t_class_words : b65t_class.all (fun t ↦
    HurwitzPrymRex_mbeq (b65t_ew (t.2.1 ++ 0 :: t.2.2)) t.1 &&
      HurwitzPrymRex_mbeq (b65t_ew (t.2.1 ++ t.2.2)) HurwitzPrymRex_mone) = true := by
  decide +kernel

theorem b65t_columns_check : (List.finRange 4).all (fun j ↦ b65t_orbit.all (b65t_columnOk j)) = true := by
  decide +kernel

end HodgeLean.Foundations.Program
