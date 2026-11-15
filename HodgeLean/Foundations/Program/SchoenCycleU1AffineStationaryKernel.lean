import HodgeLean.Foundations.Program.SchoenCycleU1SpecOverMapInjectivity
import HodgeLean.Foundations.Program.SchoenCycleU1SpecAlgebraPointInjectivity
import HodgeLean.Foundations.Program.SchoenCycleU1AffinePointMaps
import HodgeLean.Foundations.Program.SchoenCycleU1DualDifference

/-! # Actual scheme stationary kernels on affine chart algebra points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Point separation and the actual scheme stationary-kernel test separate
all dual-number algebra points on each monomorphic affine source chart.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, linearity of tangent maps. -/
theorem s2e_u1_affine_injective_of_scheme_stationary_kernel
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (hpoint : Function.Injective (Point.map f))
    (hkernel : ∀ u : s2e_u1_specOver (DualNumber ℂ) ⟶ X,
      u ≫ f = s2e_u1_constantDualPoint Y
        (Point.map f (Point.map u s2e_u1_dualResiduePoint)) →
      u = s2e_u1_constantDualPoint X (Point.map u s2e_u1_dualResiduePoint))
    (A R : Type) [CommRing A] [CommRing R] [Algebra ℂ A] [Algebra ℂ R]
    (j : R →ₐ[ℂ] A) (i : s2e_u1_specOver A ⟶ X) [Mono i.left]
    (r : s2e_u1_specOver R ⟶ Y)
    (hcomm : i ≫ f = s2e_u1_specOverMap j ≫ r) :
    Function.Injective (fun φ : A →ₐ[ℂ] DualNumber ℂ => φ.comp j) := by
  apply s2e_u1_injective_of_stationary_dual_kernel j
  · intro e e' he
    have hp : Point.map f (Point.map i (s2e_u1_specAlgebraPoint A e)) =
        Point.map f (Point.map i (s2e_u1_specAlgebraPoint A e')) := by
      change Point.map (i ≫ f) (s2e_u1_specAlgebraPoint A e) =
        Point.map (i ≫ f) (s2e_u1_specAlgebraPoint A e')
      simp only [hcomm, Point.map_comp_apply, s2e_u1_specAlgebraPoint_map, he]
    have hs := congrArg Over.Hom.left (hpoint hp)
    have hpt : s2e_u1_specAlgebraPoint A e = s2e_u1_specAlgebraPoint A e' := by
      apply Over.OverMorphism.ext
      exact (cancel_mono i.left).mp hs
    exact s2e_u1_specAlgebraPoint_injective A hpt
  · intro e φ hred hcomp
    let u := s2e_u1_specOverMap φ ≫ i
    have hb : Point.map u s2e_u1_dualResiduePoint =
        Point.map i (s2e_u1_specAlgebraPoint A e) := by
      change Point.map i (Point.map (s2e_u1_specOverMap φ) s2e_u1_dualResiduePoint) = _
      rw [s2e_u1_dualResiduePoint_specOverMap, hred]
    have hbe : Point.map f (Point.map i (s2e_u1_specAlgebraPoint A e)) =
        Point.map r (s2e_u1_specAlgebraPoint R (e.comp j)) := by
      change Point.map (i ≫ f) (s2e_u1_specAlgebraPoint A e) = _
      simp only [hcomm, Point.map_comp_apply, s2e_u1_specAlgebraPoint_map]
    have hu : u ≫ f = s2e_u1_constantDualPoint Y
        (Point.map f (Point.map u s2e_u1_dualResiduePoint)) := by
      rw [hb, hbe]
      change (s2e_u1_specOverMap φ ≫ i) ≫ f = _
      rw [Category.assoc, hcomm, ← Category.assoc, s2e_u1_specOverMap_comp, hcomp,
        ← s2e_u1_constantDualPoint_specAlgebraPoint, s2e_u1_constantDualPoint_map]
    have hu' := hkernel u hu
    have hmaps : s2e_u1_specOverMap φ ≫ i =
        s2e_u1_specOverMap ((TrivSqZeroExt.inlAlgHom ℂ ℂ ℂ).comp e) ≫ i := by
      change u = _
      rw [hu', hb, ← s2e_u1_constantDualPoint_map,
        s2e_u1_constantDualPoint_specAlgebraPoint]
    apply s2e_u1_specOverMap_injective
    apply Over.OverMorphism.ext
    exact (cancel_mono i.left).mp (congrArg Over.Hom.left hmaps)

end HodgeLean.Foundations.Program
