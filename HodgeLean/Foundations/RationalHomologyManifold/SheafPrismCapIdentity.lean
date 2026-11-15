import HodgeLean.Foundations.RationalHomologyManifold.PrismCapIdentity
import HodgeLean.Foundations.RationalHomologyManifold.PrismDegreeTransport
import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionBoundary
import HodgeLean.Foundations.RationalHomologyManifold.CapIntegerSigns

/-! The literal finite prism-cap identity in actual supported-chain sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Each finite prism cap satisfies the original boundary identity after actual stage-zero supported-chain projection.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_cap_prism_identity (X : TopCat.{0}) (p q m : ℕ)
    (U : Opens X) (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (z : (SingularChainComplex ℚ X).X (p + q))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (p + q) j z = 0) :
    subdivisionAmbientSectionMap X q U 0 (cap ℚ p q φ z) =
      subdivisionAmbientSectionMap X q U 0
        (cap ℚ p q φ ((rationalSubdivisionIterate X m).f (p + q) z)) -
      subdivisionAmbientSectionMap X q U 0
        (cap ℚ (p + 1) q (coboundary ℚ p φ) (rationalPrismSum X (p + q) (p + 1 + q) m z)) -
      (-1 : ℤ) ^ p • (((subdivisionLimitSheafComplex X).d (q + 1) q).hom.app (Opposite.op U))
        (subdivisionAmbientSectionMap X (q + 1) U 0
          (cap ℚ p (q + 1) φ (rationalPrismSum X (p + q) (p + q + 1) m z))) := by
  let w := cap ℚ p (q + 1) φ (rationalPrismSum X (p + q) (p + q + 1) m z)
  let a := cap ℚ p q φ ((rationalSubdivisionIterate X m).f (p + q) z)
  let b := cap ℚ (p + 1) q (coboundary ℚ p φ) (rationalPrismSum X (p + q) (p + 1 + q) m z)
  have hb := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_boundary X q 0 U) w
  let f : ChainGroup ℚ (TopCat.toSSet.obj X) q →+
      ((subdivisionLimitSheafComplex X).X q).obj.obj (Opposite.op U) :=
    (subdivisionAmbientSectionMap X q U 0).hom
  have hs := map_cap_sign f p (boundary ℚ q w)
  have hh := congrArg (subdivisionAmbientSectionMap X q U 0)
    (rationalPrismSum_cap_identity X p q m φ z hz)
  rw [rationalPrismSum_reassoc] at hh
  simp only [map_sub] at hh
  have ht := hs.trans (congrArg (fun t => (-1 : ℤ) ^ p • t) hb.symm)
  exact hh.trans (congrArg (fun t => subdivisionAmbientSectionMap X q U 0 a -
    subdivisionAmbientSectionMap X q U 0 b - t) ht)

#print axioms subdivisionAmbientSection_cap_prism_identity
end HodgeLean.Foundations.RationalHomologyManifold
