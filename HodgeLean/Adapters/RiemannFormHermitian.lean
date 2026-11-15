import HodgeLean.Adapters.RiemannFormHermitianProofs

/-! # The Riemann relations: `H` from `E` (frozen specification)

Scope (Appell–Humbert stage 4b). Stage 4a (`AutomorphyChernHQ`) builds `datumOfX X H E hE χ hχ`
on the S12 period lattice `Λ = abelianPeriodLattice X ⊆ ℂ^g` from a Hermitian form `H` given as
an input with `Im H = E` on `Λ`. This module removes `H` as an input. The convention for `H` is the
repository's: conjugate-linear in the first argument (`HermitianForm`). Claimed:
* every Hermitian form is determined by its imaginary part, `H(v, w) = Im H(v, iw) + i Im H(v, w)`,
  and `Im H` is real-bilinear;
* an integral form `E` on a full lattice `L` extends uniquely to a real-bilinear form `B` on the
  ambient space, alternating when `E` is;
* a Hermitian form is determined by the values of `Im H` on `L`, and then `Im H = B` everywhere;
* `E = Im H` on `L` for some `H` iff `E` is alternating and `B(iv, iw) = B(v, w)` (the Riemann
  relation for the real extension), as an implication from `spec_appellHumbert_riemann_relations`;
  with the uniqueness statement this is the bijection of Birkenhake–Lange, Lemma 1.3.1, at the
  level of lattices;
* falsification: in complex dimension one every alternating real form satisfies the Riemann
  relation, so a witness needs `ℂ²`; the integral alternating form `n₀ m₂ - n₂ m₀` on the Gaussian
  lattice `ℤ[i]² ⊆ ℂ²` is `Im H` on the lattice for no `H`;
* on `X`'s period lattice, as an implication from stage 4a: from `E` alone, under the Riemann
  relation, there is `H` with `Im H = B` and a datum `datumOfX` whose integral form is `E`; and if
  moreover `B(v, iv) > 0` for `v ≠ 0`, that `H` is positive definite and Hard Lefschetz holds for
  `latticeClassHQ X E` and for the class of the Chern form of every such datum.

Not claimed: that the datum defines a line bundle on the scheme `X` or that its class is algebraic
(GAGA); `LefschetzOneOneHyp`; that `ℂ^g / Λ ≅ X(ℂ)` as complex manifolds; that every integral
alternating form on `Λ` satisfies the Riemann relation (it does not, see the falsification).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass

namespace HodgeLean.Adapters

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]

/-- A Hermitian form (conjugate-linear in its first argument) is recovered from its imaginary
part: `Re H(v, w) = Im (i H(v, w)) = Im H(v, iw)`. In Birkenhake–Lange's convention (linear in the
first argument) the same identity reads `H(v, w) = E(iv, w) + i E(v, w)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1; `HermitianForm`. -/
theorem spec_hermitian_toFun_eq_imaginary (H : HermitianForm (V := V)) (v w : V) :
    H.toFun v w = (H.imaginary v (Complex.I • w) : ℂ) + (H.imaginary v w : ℂ) * Complex.I :=
  spec_hermitian_toFun_eq_imaginary_aux H v w

example (H : HermitianForm (V := V)) (v : V) :
    (H.toFun v v).re = H.imaginary v (Complex.I • v) := by
  rw [spec_hermitian_toFun_eq_imaginary H v v]
  simp

/-- The imaginary part of a Hermitian form is real-bilinear.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1; `HermitianForm`. -/
theorem spec_hermitian_imaginary_bilinear (H : HermitianForm (V := V)) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, ∀ v w, B v w = H.imaginary v w :=
  spec_hermitian_imaginary_bilinear_aux H

example (H : HermitianForm (V := V)) (r : ℝ) (v w : V) :
    H.imaginary (r • v) w = r * H.imaginary v w := by
  obtain ⟨B, hB⟩ := spec_hermitian_imaginary_bilinear H
  rw [← hB, ← hB, map_smul, LinearMap.smul_apply, smul_eq_mul]

end Forms

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- An integral form on a full lattice `L ⊆ V` extends uniquely to a real-bilinear form on `V`:
a `ℤ`-basis of `L` is an `ℝ`-basis of `V` (`Basis.ofZLatticeBasis`), so the extension is the
bilinear form with the same Gram matrix, and it is unique because `L` spans `V` over `ℝ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.1
(`E` extended `ℝ`-bilinearly to `Λ ⊗ ℝ = V`); `Basis.ofZLatticeBasis`, `IsZLattice.span_top`. -/
theorem spec_exists_unique_realExtension (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) :
    ∃! B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, ∀ l m : L, B l m = E l m :=
  spec_exists_unique_realExtension_aux L E

example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (E : L →+ L →+ ℤ)
    (B B' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = E l m)
    (hB' : ∀ l m : L, B' l m = E l m) : B = B' :=
  (spec_exists_unique_realExtension L E).unique hB hB'

/-- The real extension of an alternating integral form is alternating: `E` is antisymmetric on
`L`, so `B` is antisymmetric on an `ℝ`-basis, hence alternating.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1;
`spec_exists_unique_realExtension`. -/
theorem spec_realExtension_alternating (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) (hE : ∀ l : L, E l l = 0)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = E l m) (v : V) : B v v = 0 :=
  spec_realExtension_alternating_aux L E hE B hB v

example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (E : L →+ L →+ ℤ)
    (hE : ∀ l : L, E l l = 0) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = E l m) :
    ∀ v w, B v w = -B w v := by
  intro v w
  have h := spec_realExtension_alternating L E hE B hB (v + w)
  simp only [map_add, LinearMap.add_apply,
    spec_realExtension_alternating L E hE B hB v,
    spec_realExtension_alternating L E hE B hB w] at h
  linarith

/-- Uniqueness in the Riemann correspondence: a Hermitian form is determined by the values of its
imaginary part on a full lattice, since `Im H` is real-bilinear, `L` spans `V` over `ℝ`, and `H` is
recovered from `Im H` (`spec_hermitian_toFun_eq_imaginary`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and §2.1;
`spec_hermitian_toFun_eq_imaginary`, `spec_hermitian_imaginary_bilinear`. -/
theorem spec_hermitian_eq_of_imaginary_lattice (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (H H' : HermitianForm (V := V))
    (h : ∀ l m : L, H.imaginary l m = H'.imaginary l m) : H = H' :=
  spec_hermitian_eq_of_imaginary_lattice_aux L H H' h

example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (E : L →+ L →+ ℤ)
    (H H' : HermitianForm (V := V)) (hE : ∀ l m : L, (E l m : ℝ) = H.imaginary l m)
    (hE' : ∀ l m : L, (E l m : ℝ) = H'.imaginary l m) : H = H' :=
  spec_hermitian_eq_of_imaginary_lattice L H H' fun l m ↦ by rw [← hE, ← hE']

/-- If `E = Im H` on a full lattice, then `Im H` is the real extension of `E` on all of `V`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and §2.1;
`spec_exists_unique_realExtension`, `spec_hermitian_imaginary_bilinear`. -/
theorem spec_imaginary_eq_realExtension (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ l m : L, B l m = E l m) (H : HermitianForm (V := V))
    (hE : ∀ l m : L, (E l m : ℝ) = H.imaginary l m) (v w : V) : H.imaginary v w = B v w :=
  spec_imaginary_eq_realExtension_aux L E B hB H hE v w

example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (E : L →+ L →+ ℤ)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = E l m) (H : HermitianForm (V := V))
    (hE : ∀ l m : L, (E l m : ℝ) = H.imaginary l m) :
    H.IsPositiveDefinite ↔ ∀ v, v ≠ 0 → 0 < B v (Complex.I • v) := by
  simp only [HermitianForm.IsPositiveDefinite, spec_hermitian_toFun_eq_imaginary H,
    spec_imaginary_eq_realExtension L E B hB H hE]
  simp

/-- The Riemann relations on a full lattice: an integral form `E` on `L` is `Im H` on `L` for some
Hermitian `H` iff `E` is alternating and its real extension `B` satisfies `B(iv, iw) = B(v, w)`.
An implication from `spec_appellHumbert_riemann_relations` (applied to `B`), with
`spec_realExtension_alternating` and `spec_imaginary_eq_realExtension`; the `H` is unique by
`spec_hermitian_eq_of_imaginary_lattice`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and §2.1;
`spec_appellHumbert_riemann_relations`. -/
theorem spec_exists_hermitian_iff_riemann (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ l m : L, B l m = E l m) :
    (∃ H : HermitianForm (V := V), ∀ l m : L, (E l m : ℝ) = H.imaginary l m) ↔
      (∀ l : L, E l l = 0) ∧ IsTypeOneOne (fun v w ↦ B v w) :=
  spec_exists_hermitian_iff_riemann_aux L E B hB

example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (E : L →+ L →+ ℤ)
    (hE : ∀ l : L, E l l = 0) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = E l m)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    ∃! H : HermitianForm (V := V), ∀ l m : L, (E l m : ℝ) = H.imaginary l m := by
  obtain ⟨H, hH⟩ := (spec_exists_hermitian_iff_riemann L E B hB).2 ⟨hE, h11⟩
  exact ⟨H, hH, fun H' hH' ↦
    spec_hermitian_eq_of_imaginary_lattice L H' H fun l m ↦ by rw [← hH, ← hH']⟩

end Lattice

section Falsification

/-- In complex dimension one the Riemann relation is automatic: an alternating real form on
`ℂ ≅ ℝ²` is a multiple of the determinant, and multiplication by `i` has determinant `1`. So a
falsification of the Riemann relation for an integral alternating form needs `g ≥ 2`; none exists
on a lattice `ℤ² ⊆ ℂ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and §2.1 (every
elliptic curve is polarized); `IsTypeOneOne`. -/
theorem spec_isTypeOneOne_of_alternating_complex (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ)
    (hB : ∀ v, B v v = 0) : IsTypeOneOne (fun v w ↦ B v w) :=
  spec_isTypeOneOne_of_alternating_complex_aux B hB

example (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ) (hB : ∀ v, B v v = 0) :
    B (Complex.I • 1) (Complex.I • Complex.I) = B 1 Complex.I :=
  spec_isTypeOneOne_of_alternating_complex B hB 1 Complex.I

/-- Falsification: the integral alternating form `E(n, m) = n₀ m₂ - n₂ m₀` on the Gaussian lattice
`ℤ[i]² ⊆ ℂ²` (coordinates `gaussPoint`) has real extension `Re v₀ Re w₁ - Re v₁ Re w₀`, the
non-Riemann form of `spec_nonRiemann_form_counterexample`, and it is `Im H` on the lattice for no
Hermitian `H`: with `v = (1,0)`, `w = (0,1)`, `E(v, w) = 1` while `E(iv, iw) = 0`, but
`Im H(iv, iw) = Im H(v, w)` for every `H`. So the Riemann relation premise of
`spec_exists_hermitian_iff_riemann` cannot be dropped.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1;
`spec_nonRiemann_form_counterexample`. -/
theorem spec_nonRiemann_lattice_falsification :
    let E : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℤ := fun n m ↦ n 0 * m 2 - n 2 * m 0
    (∀ n, E n n = 0) ∧
      (∀ n m, (E n m : ℝ) = (gaussPoint n 0).re * (gaussPoint m 1).re -
        (gaussPoint n 1).re * (gaussPoint m 0).re) ∧
      ¬ ∃ H : HermitianForm (V := Fin 2 → ℂ), ∀ n m,
        (E n m : ℝ) = H.imaginary (gaussPoint n) (gaussPoint m) :=
  spec_nonRiemann_lattice_falsification_aux

example : ¬ ∃ H : HermitianForm (V := Fin 2 → ℂ), ∀ n m : Fin 4 → ℤ,
    ((n 0 * m 2 - n 2 * m 0 : ℤ) : ℝ) = H.imaginary (gaussPoint n) (gaussPoint m) :=
  spec_nonRiemann_lattice_falsification.2.2

end Falsification

section Abelian

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- `datumOfX` from `E` alone: on `X`'s period lattice, an alternating integral form `E` whose real
extension `B` satisfies the Riemann relation `B(iv, iw) = B(v, w)` is `Im H` for a Hermitian `H`
with `Im H = B`, and there is a semicharacter `χ` making `datumOfX X H E hE χ hχ` a datum with
integral form `E`. An implication from `spec_exists_hermitian_iff_riemann` and stage 4a
(`spec_exists_semicharacterOfX`, `spec_datumOfX_imForm`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1, §2.2 and
Theorem 2.2.3; `spec_exists_semicharacterOfX`, `spec_datumOfX_imForm`. -/
theorem spec_exists_datumOfX_of_riemann
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
      (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m),
      (∀ v w, H.imaginary v w = B v w) ∧
      ∃ (χ : abelianPeriodLattice X → Circle)
        (hχ : ∀ l m : abelianPeriodLattice X,
          χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)),
        (datumOfX X H E hE χ hχ).imForm = E :=
  spec_exists_datumOfX_of_riemann_aux X E hEalt B hB h11

example (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    ∃ D : Datum (V := Fin (dim X.left) → ℂ), D.lattice = abelianPeriodLattice X := by
  obtain ⟨H, hE, -, χ, hχ, -⟩ := spec_exists_datumOfX_of_riemann X E hEalt B hB h11
  exact ⟨datumOfX X H E hE χ hχ, rfl⟩

/-- Hard Lefschetz from `E` alone: if moreover `B(v, iv) > 0` for `v ≠ 0` (positivity of
`Re H(v, v) = Im H(v, iv)`), the Hermitian form with `Im H = B` is positive definite, Hard
Lefschetz holds for `latticeClassHQ X E`, and it holds for the class of the Chern form of every
datum `datumOfX X H E hE χ hχ` and every continuous logarithm of its factor. An implication from
`spec_exists_hermitian_iff_riemann`, `spec_latticeClassHQ_hardLefschetz` and stage 4a's
`spec_chernClassHQ_datumOfX_hardLefschetz`; it does not say the class is algebraic.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1, Theorem 2.2.3 and
§4.1; Huybrechts, *Complex Geometry*, Proposition 3.3.13;
`spec_chernClassHQ_datumOfX_hardLefschetz`. -/
theorem spec_chernClassHQ_hardLefschetz_of_riemann
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (h11 : IsTypeOneOne (fun v w ↦ B v w))
    (hpos : ∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) :
    HardLefschetz X (cupProductOf X) (latticeClassHQ X E) ∧
      ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
        (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m),
        H.IsPositiveDefinite ∧ (∀ v w, H.imaginary v w = B v w) ∧
        ∀ (χ : abelianPeriodLattice X → Circle)
          (hχ : ∀ l m : abelianPeriodLattice X,
            χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
          (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ),
          (∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
            Complex.exp (2 * Real.pi * Complex.I * f l v)) →
          (∀ l, Continuous (f l)) →
          ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
            (∀ l m, E' l m = chernForm f l m) ∧
              HardLefschetz X (cupProductOf X) (latticeClassHQ X E') :=
  spec_chernClassHQ_hardLefschetz_of_riemann_aux X E hEalt B hB h11 hpos

example (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (h11 : IsTypeOneOne (fun v w ↦ B v w))
    (hpos : ∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) :
    ∃ η : HQ X 2, HardLefschetz X (cupProductOf X) η := by
  obtain ⟨-, H, hE, -, -, hL⟩ :=
    spec_chernClassHQ_hardLefschetz_of_riemann X E hEalt B hB h11 hpos
  obtain ⟨χ, hχ⟩ := spec_exists_semicharacterOfX X H E hE
  obtain ⟨E', -, hE'⟩ := hL χ hχ _ (spec_holLog_isLog _).1
    (spec_holLog_isLog (datumOfX X H E hE χ hχ)).2
  exact ⟨_, hE'⟩

end Abelian

end HodgeLean.Adapters
