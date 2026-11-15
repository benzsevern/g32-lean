import HodgeLean.Papers.G32TransferDefs
import HodgeLean.Papers.PapersG32Certificates
import HodgeLean.Papers.PapersArithmetic
import Mathlib.LinearAlgebra.Basis.Defs

/-! # G32 Theorem A, stage 5: discriminant definitions

This file records the premise comparing the geometric polarization form on a fibre with the
parabolic cup-product form computed by the explicit cocycle matrix. -/

noncomputable section

open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.HermitianForm
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **Parabolic-polarization comparison (premise).** In a basis of the fibre's Weil Hermitian
space, its Gram matrix is a positive rational multiple of the parabolic cup-product matrix
`g32H0`. This is the basis-level comparison between geometric cohomology and the explicit
cocycle calculation.
Source: G32 v0.16, Section 6 and Proposition 6.3; the finite-cover derivation of the parabolic
cup-product polarization. -/
def g32d_ParabolicPolarization {P : g32t_Sixfold}
    (h : g32t_PolarizedWeil P) : Prop :=
  let hT := torusCohomology_cupProductOf P.X
  letI := hT.finite
  let E := polarizationForm hT h.nondegenerate
  let J := ⟨P.W.J, P.W.J_sq⟩
  let H := weilHermitian E J
    (by simpa [E, polarizationForm] using
      (isRosatiSkew_iff_dualForm h.nondegenerate P.W.J).1 h.rosati)
  let ζ : QuadraticAlgebra ℚ (-3) 0 :=
    (-1 + QuadraticAlgebra.omega) / 2
  ∃ c : {c : ℚ // 0 < c},
    ∃ e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ P.X 1) J),
      LinearMap.toMatrix₂ e e H =
        ((c : ℚ) : QuadraticAlgebra ℚ (-3) 0) • g32H0 ζ

/-- The comparison premise supplies a basis carrying the geometric Gram form to the scaled
printed matrix. -/
example {P : g32t_Sixfold} (h : g32t_PolarizedWeil P)
    (H : g32d_ParabolicPolarization h) :
    let hT := torusCohomology_cupProductOf P.X
    letI := hT.finite
    let E := polarizationForm hT h.nondegenerate
    let J := ⟨P.W.J, P.W.J_sq⟩
    let Hform := weilHermitian E J
      (by simpa [E, polarizationForm] using
        (isRosatiSkew_iff_dualForm h.nondegenerate P.W.J).1 h.rosati)
    let ζ : QuadraticAlgebra ℚ (-3) 0 := (-1 + QuadraticAlgebra.omega) / 2
    ∃ c : {c : ℚ // 0 < c},
      ∃ e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ P.X 1) J),
        LinearMap.toMatrix₂ e e Hform =
          ((c : ℚ) : QuadraticAlgebra ℚ (-3) 0) • g32H0 ζ :=
  H

end HodgeLean.Papers
