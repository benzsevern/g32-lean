import HodgeLean.Foundations.Program.PrymParabolicIntersectionDualGlobal
import HodgeLean.Foundations.Program.CurveJacobianRestUnique

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The cup product on the orientation cycle from duality of the barycentric dual cycle: if the
dual cycle of `φ` pairs with every cycle `z` as `φ z`, the cup product of `φ` and `ψ` is
`−Q(P a, P b)`.
Source: Hatcher, *Algebraic Topology*, §3.3, cap product and Poincaré duality. -/
theorem hga_aw_intersection_of_duality {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] (F : hg8_DeltaMap b4b_root T)
    (P : b6m_H1 T →ₗ[ℤ] b3_periodLattice ℂ T)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ T)) (hQ : b3_IsIntersectionForm ℂ Q)
    (φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ ∘ₗ Simplicial.boundary ℤ 1 = 0) (hψ : ψ ∘ₗ Simplicial.boundary ℤ 1 = 0)
    (a b : b6m_H1 T)
    (ha : ∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom,
      φ z.1 = Q (P a) (P (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z)))
    (hb : ∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom,
      ψ z.1 = Q (P b) (P (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z)))
    (hdual : ∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom,
      Q (P (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
          (hga_dual_fundCycle F φ hφ)))
        (P (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z)) = φ z.1) :
    HodgeLean.Foundations.Singular.cupCochain (TopCat.of T) 1 1 φ ψ (hga_fundChain F) =
      -Q (P a) (P b) := by
  let K := (SingularChainComplex ℤ (TopCat.of T)).sc 1
  obtain ⟨zb, rfl⟩ := K.moduleCatHomologyClass_surjective b
  rw [hga_cup_fundChain_eq_dual_evaluation F φ ψ hφ hψ]
  change ψ (hga_dual_fundCycle F φ hφ).1 = _
  rw [hb, b3Rest_intersectionForm_skew (E := ℂ) (Module.finrank_self ℂ) Q hQ, hdual zb, ha zb]

end HodgeLean.Foundations.Program
