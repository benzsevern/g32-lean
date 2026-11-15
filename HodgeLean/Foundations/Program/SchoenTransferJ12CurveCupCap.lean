import HodgeLean.Foundations.Program.SchoenTransferJ12CapPairing
import HodgeLean.Foundations.RationalHomologyManifold.Basic
import HodgeLean.Adapters.CupProductOf

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.QuotientDuality HodgeLean.Foundations.RationalHomologyManifold
namespace HodgeLean.Foundations.Program

/-- The singular cup evaluation agrees with the cap pairing, with the same factor order.
Source: Hatcher, Algebraic Topology, §3.3, cup-cap evaluation identity. -/
theorem s4_selected_localTracePairing_cup (T : TopCat.{0}) (p q : ℕ)
    (c : Homology ℚ T (p + q)) (a : Cohomology ℚ T p) (b : Cohomology ℚ T q) :
    localTracePairing T p q c a b =
      cohomologyEquivDualHomology ℚ T (p + q) (Singular.cup T rfl a b) c :=
  s4_selected_cap_cup_pairing T p q a b c

/-- A normalized top class detects degree-one classes through the actual cup product.
Source: Hatcher, Algebraic Topology, Theorem 3.30 and §3.3. -/
theorem s4_selected_curve_cup_of_triangulation
    (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (t : FiniteTriangulation (TopCat.of (ComplexPoint Y)))
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint Y)) (1 + 1))
    [FiniteDimensional ℚ (Cohomology ℚ (TopCat.of (ComplexPoint Y)) 1)]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (v : HQ Y 1)
    (hv : ∀ w : HQ Y 1, I ((cupProductOf Y).cup rfl v w) = 0) : v = 0 := by
  let T := TopCat.of (ComplexPoint Y)
  let := pathConnectedSpace_complexPoint Y
  obtain ⟨c, hc⟩ := fundamental_exists T t (1 + 1) o
  have hinj := (localTracePairing_bijective_of_cap T 1 c
    (cap_duality T t 1 1 o c hc)).1
  apply (cupComparison Y 1).injective
  rw [map_zero]
  apply hinj
  ext b
  obtain ⟨w, rfl⟩ := (cupComparison Y 1).surjective b
  have hcup : (cupProductOf Y).cup rfl v w = 0 :=
    I.injective ((hv w).trans (map_zero I).symm)
  rw [s4_selected_localTracePairing_cup, ← cupComparison_cup Y rfl v w, hcup,
    map_zero, map_zero]
  simp only [map_zero, LinearMap.zero_apply]

end HodgeLean.Foundations.Program
