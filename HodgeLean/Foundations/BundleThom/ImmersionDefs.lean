import HodgeLean.Foundations.BundleThom.AnalyticNormal
import HodgeLean.Foundations.BundleThom.NeighbourhoodDefs
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # The actual smooth-neighbourhood factorization

The factorization retains its scheme maps and the supported class remains on
the original ambient scheme.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

/-- The specified factor through the actual smooth ambient neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.8; Bott–Tu, §6. -/
def i1_smoothLift {Q W : Over (Spec ↧ℂ)} (ι : Q ⟶ W)
    {V : Scheme} (v : V ⟶ W.left) (j : Q.left ⟶ V) (hj : j ≫ v = ι.left) :
    Q ⟶ Over.mk (v ≫ W.hom) :=
  Over.homMk j (by
    change j ≫ (v ≫ W.hom) = Q.hom
    rw [← Category.assoc, hj]
    exact Over.w ι)

/-- The analytic map from a tubular chart back to the original ambient scheme.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6. -/
def i1_tubularAmbientMap {Q W : Over (Spec ↧ℂ)} {V : Scheme}
    (v : V ⟶ W.left) (j : Q.left ⟶ V) (k : ℕ)
    [TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j))]
    (U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
    (T : Opens (ComplexPoint (Over.mk (v ≫ W.hom)))) (h : U ≃ₜ T) :
    C(U, ComplexPoint W) :=
  (Point.continuousMap (Over.homMk v rfl)).comp
    (⟨Subtype.val, continuous_subtype_val⟩ : C(T, _)) |>.comp ⟨h, h.continuous⟩

example {Q W : Over (Spec ↧ℂ)} (ι : Q ⟶ W) {V : Scheme}
    (v : V ⟶ W.left) (j : Q.left ⟶ V) (hj : j ≫ v = ι.left) :
    (i1_smoothLift ι v j hj).left = j := rfl

example {Q W : Over (Spec ↧ℂ)} {V : Scheme} (v : V ⟶ W.left)
    (j : Q.left ⟶ V) (k : ℕ)
    [TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j))]
    (U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
    (T : Opens (ComplexPoint (Over.mk (v ≫ W.hom)))) (h : U ≃ₜ T) (z : U) :
    i1_tubularAmbientMap v j k U T h z =
      Point.map (Over.homMk v rfl) (h z).1 := rfl

end HodgeLean.Foundations.BundleThom
