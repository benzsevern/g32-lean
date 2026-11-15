import HodgeLean.Foundations.Program.PrymParabolicIntersectionLocalDegree

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Inverse wedge coordinates on the punctured complex line.
Source: `hga_wedgeDeformation_inverse`. -/
def hga_wedgeInversePairMap (u v : ℝ) (huv : u < v) :
    puncturedPair ℂ 1 ⟶ puncturedPair ℂ 1 :=
  hga_complexScalarPairMap
    ⟨hga_wedgeInverse u v, (hga_wedgeHomeomorph u v huv).continuous_invFun⟩ (by
      intro z hz h
      change hga_wedgeInverse u v z = 0 at h
      apply hz
      calc
        z = hga_wedgeDeformation u v 1 (hga_wedgeInverse u v z) :=
          (hga_wedgeDeformation_inverse u v huv z).symm
        _ = 0 := by rw [h]; simp [hga_wedgeDeformation])

set_option backward.isDefEq.respectTransparency false in
theorem hga_wedgeLift_localClass {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] [CompactSpace T] [ConnectedSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hinj : Function.Injective σ)
    (u v : ℝ) (huv : u < v) (k : T → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (c : ℂ)
    (hp : ∀ᶠ z : ℂ in 𝓝 0, k (hga_wedgeLift σ u v z) = ((z + c : ℂ) : OnePoint ℂ)) :
    relativeHomologyMap ℤ 2
      (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap σ hinj
        (hga_triangleRetraction 0) hga_triangleRetraction_zero_weights)
      (standardComplexLocalClass ℤ 1) =
      -b6m_surfaceLocalClass ℤ (σ (hga_triangleRetraction 0)) := by
  let F := hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap σ hinj
    (hga_triangleRetraction 0) hga_triangleRetraction_zero_weights
  let Q := hga_wedgeInversePairMap u v huv ≫ F
  have hQ : relativeHomologyMap ℤ 2 Q (standardComplexLocalClass ℤ 1) =
      b6m_surfaceLocalClass ℤ (σ (hga_triangleRetraction 0)) :=
    hga_planeLift_localClass _ (hga_wedgeLift σ u v) (hga_wedgeLift_zero σ u v)
      k hk c hp Q (fun z ↦ rfl)
  have hm : relativeHomologyMap ℤ 2 (hga_wedgePairMap u v huv 1 ≫ Q) =
      relativeHomologyMap ℤ 2 F := by
    apply hga_local_maps_eq_of_eventuallyEq ℤ _ 1 2
    apply Filter.Eventually.of_forall
    intro z
    change hga_triangleExtension σ
      (hga_wedgeInverse u v (hga_wedgeDeformation u v 1 (z 0))) =
      hga_triangleExtension σ (z 0)
    rw [hga_wedgeInverse_deformation u v huv]
  change relativeHomologyMap ℤ 2 F (standardComplexLocalClass ℤ 1) = _
  rw [← hm, relativeHomologyMap_comp, LinearMap.comp_apply,
    hga_wedgePairMap_standardLocalClass, map_neg, hQ]

#print axioms hga_wedgeLift_localClass

#print axioms hga_wedgeInversePairMap
end HodgeLean.Foundations.Program
