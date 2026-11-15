import HodgeLean.Foundations.Program.G32Native.RetainedFrameInverseCoordinates
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanSectionAgreement

/-! # Differentiated representatives and their original normal frame formula -/
noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Bundle
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

private local instance normalTotalTop {Y : Over (Spec ↧ℂ)} {X : Scheme}
    (j : Y.left ⟶ X) (k : ℕ) :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Differentiating the embedding on the supplied representatives, in each
point's original ambient chart. -/
def retainedEuclideanDisplacement
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) (d k n : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (L : ∀ x : ComplexPoint Y, i1_normalFibre j.left x →ₗ[ℂ] (Fin d → ℂ))
    (p : TotalSpace (Fin k → ℂ) (i1_normalFibre j.left)) : EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (fun c => emb ((chartAt (Fin d → ℂ) (Point.map j p.proj)).symm c))
    ((chartAt (Fin d → ℂ) (Point.map j p.proj)) (Point.map j p.proj)) (L p.proj p.2)

theorem retained_euclidean_displacement_frame_formula
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k n : ℕ) [SmoothOfRelativeDimension d X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (A : X.left.Opens) (hA : IsAffineOpen A) (U : Y.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Y) (hxU : x ∈ Point.overOpen U)
    (hxA : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hi : Function.Injective (retainedAffineConormalDifferential X Y j d A hA x hxA z hz))
    (L : ∀ y : ComplexPoint Y, i1_normalFibre j.left y →ₗ[ℂ] (Fin d → ℂ))
    (Lz : i1_normalFibre j.left x →ₗ[ℂ] (Fin d → ℂ))
    (hL : ∀ u, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hxA
      (Point.map j x) (mem_chart_source _ _) a (L x u) = u a) ∧
      ∀ t, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hxA
        (Point.map j x) (mem_chart_source _ _) a t = 0) →
      g.coefficient (Point.map j x) ((chartAt (Fin d → ℂ) (Point.map j x)) (Point.map j x)) (L x u) t = 0)
    (hLz : ∀ u, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hxA z hz a (Lz u) = u a) ∧
      ∀ t, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hxA z hz a t = 0) →
        g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x)) (Lz u) t = 0)
    (w : Fin k → ℂ) :
    retainedEuclideanDisplacement X Y j d k n emb L
      ((i1_normalFrameTrivialization j.left k U E).toOpenPartialHomeomorph.symm (x, w)) =
      fderiv ℝ (fun a => emb ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) (Point.map j x))
        (Lz ((i1_conormalFrameBasis j.left k U E x hxU).dualBasis.equivFun.symm w)) := by
  rw [retained_normal_frame_inverse j.left k U E x hxU w]
  change fderiv ℝ (fun a => emb ((chartAt (Fin d → ℂ) (Point.map j x)).symm a))
    ((chartAt (Fin d → ℂ) (Point.map j x)) (Point.map j x)) (L x _) = _
  exact retained_euclidean_sections_change_chart X Y j d n g emb hemb A hA x hxA
    (Point.map j x) z (mem_chart_source _ _) hz hi (L x) Lz hL hLz _

#print axioms retained_euclidean_displacement_frame_formula
end HodgeLean.Foundations.TubularEuler
