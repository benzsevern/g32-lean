import HodgeLean.Adapters.LatticeClassHQDefs
import HodgeLean.Foundations.AutomorphyChernClassDefs

/-! # The Chern form in `HQ X 2` on `X`'s own period lattice: definitions (FROZEN)

An Appell–Humbert datum whose lattice is the S12 period lattice `Λ = abelianPeriodLattice X` of
an abelian `X`, built from a Hermitian form `H` on `ℂ^g` (`g = dim X.left`), an integral form `E`
on `Λ` with `E = Im H` on `Λ`, and a semicharacter `χ` for `H`. Nothing here says the datum
defines a line bundle on the scheme `X`, or that it is algebraic.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The Appell–Humbert datum on the S12 period lattice of `X` with Hermitian form `H` and
semicharacter `χ`; the integral form `E` with `E = Im H` on `Λ` supplies integrality.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`X(ℂ) = ℂ^g / Λ`), §2.2 and
Theorem 2.2.3 (Appell–Humbert data); `abelianPeriodLattice`, `Datum`. -/
def datumOfX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    Datum (V := Fin (dim X.left) → ℂ) :=
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  { lattice := abelianPeriodLattice X
    discrete := discrete_complexExponentialLattice X (dim X.left)
    isZLattice := isZLattice_complexExponentialLattice X (dim X.left)
    hermitian := H
    integral := fun l m => ⟨E l m, (hE l m).symm⟩
    semicharacter := χ
    semicharacter_add := hχ }

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    (datumOfX X H E hE χ hχ).lattice = abelianPeriodLattice X ∧
      (datumOfX X H E hE χ hχ).hermitian = H := ⟨rfl, rfl⟩

/-- The trivial datum on the period lattice of `X`: `H = 0`, `E = 0`, `χ = 1`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 (the datum of the
trivial bundle); `datumOfX`, `HermitianForm.zero`. -/
def datumOfXTrivial : Datum (V := Fin (dim X.left) → ℂ) :=
  datumOfX X HermitianForm.zero 0
    (fun _ _ => by simp [HermitianForm.imaginary, HermitianForm.zero])
    (fun _ => 1)
    (fun _ _ => by simp [HermitianForm.imaginary, HermitianForm.zero])

example (l : abelianPeriodLattice X) (v : Fin (dim X.left) → ℂ) :
    holFactor (datumOfXTrivial X) l v = 1 := by
  simp [holFactor, datumOfXTrivial, datumOfX, HermitianForm.zero]

end HodgeLean.Adapters
