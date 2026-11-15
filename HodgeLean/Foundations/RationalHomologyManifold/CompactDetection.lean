import HodgeLean.Foundations.RationalHomologyManifold.CompactSupportBound
import HodgeLean.Foundations.QuotientDuality.LocalCompactDetection
import HodgeLean.Foundations.QuotientDuality.LocalCompactGluing

/-! Descent from the finite-polyhedron support bound to point detection.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicTopology.Singular HodgeLean.RealDefs
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Local concentration and the support dimension bound give detection on compact subsets.
Source: Bredon, Sheaf Theory, second edition, V.9 and V.16; relative Mayer–Vietoris descent.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_compact_detection (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (A : Set X) (hA : IsCompact A) : LocalHomologyDetectedByPoints X n A := by
  apply compact_detection_of_uniform_bound X n (t.ambient + 1)
    (fun x i hi => o.vanishes x i (by omega)) ?_ A hA
  exact finiteTriangulation_compact_support_bound X t

#print axioms finiteTriangulation_compact_detection
end HodgeLean.Foundations.RationalHomologyManifold
