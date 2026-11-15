import HodgeLean.Foundations.QuotientDuality.RetainedCycleAmbientCapCoboundary

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual quotient cap operation is additive in the ambient cochain. -/
theorem retained_relative_ambient_cap_add (P : TopPair.{0}) (p q : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    retainedRelativeAmbientCapHom P p q (φ + ψ) =
      retainedRelativeAmbientCapHom P p q φ + retainedRelativeAmbientCapHom P p q ψ := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap ℚ P (p + q))
  change (relativeChainProjection ℚ P).f (p + q) ≫ _ =
    (relativeChainProjection ℚ P).f (p + q) ≫ _
  rw [Preadditive.comp_add, retained_relative_projection_ambient_cap,
    retained_relative_projection_ambient_cap, retained_relative_projection_ambient_cap,
    Simplicial.capHom_add, Preadditive.add_comp]

/-- Addition of cocycles induces addition of the actual relative homology cap maps. -/
theorem retained_relative_cap_homology_add (P : TopPair.{0}) (p q : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) (hψ : Simplicial.coboundary ℚ p ψ = 0)
    (hadd : Simplicial.coboundary ℚ p (φ + ψ) = 0) :
    retainedRelativeCapHomology P p q (φ + ψ) hadd =
      retainedRelativeCapHomology P p q φ hφ + retainedRelativeCapHomology P p q ψ hψ := by
  have h : ShortComplex.homologyMap (retainedRelativeCapShortComplex P p q (φ + ψ) hadd) =
      ShortComplex.homologyMap (retainedRelativeCapShortComplex P p q φ hφ) +
        ShortComplex.homologyMap (retainedRelativeCapShortComplex P p q ψ hψ) := by
    rw [← ShortComplex.homologyMap_add]
    apply retained_homology_map_eq_of_middle
    simp only [retained_relative_cap_short_complex_middle, ShortComplex.add_τ₂]
    exact retained_relative_ambient_cap_add P p q φ ψ
  exact congrArg ModuleCat.Hom.hom h

/-- Adding an ambient coboundary leaves the actual relative homology cap map unchanged. -/
theorem retained_relative_cap_homology_eq_of_eq_add_coboundary
    (P : TopPair.{0}) (p q : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) (p + 1))
    (hφ : Simplicial.coboundary ℚ (p + 1) φ = 0)
    (hψ : Simplicial.coboundary ℚ (p + 1) ψ = 0)
    (η : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (h : φ = ψ + Simplicial.coboundary ℚ p η) :
    retainedRelativeCapHomology P (p + 1) q φ hφ =
      retainedRelativeCapHomology P (p + 1) q ψ hψ := by
  subst φ
  rw [retained_relative_cap_homology_add P (p + 1) q ψ
    (Simplicial.coboundary ℚ p η) hψ (Simplicial.coboundary_coboundary ℚ p η) hφ,
    retained_relative_cap_homology_coboundary_zero, add_zero]

end HodgeLean.Foundations.QuotientDuality
