import HodgeLean.Foundations.RationalHomologyManifold.FixedCapPresheaf
import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionBoundary
import HodgeLean.Foundations.RationalHomologyManifold.CapIntegerSigns

/-! The actual differential of fixed-cycle cap as an ambient-cochain presheaf morphism.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Literal fixed-cycle cap intertwines the ambient coboundary and supported-chain sheaf boundary with the original sign.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem ambientFixedCapPresheafMap_coboundary (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q + 1)) (hz : boundary ℚ (p + q) z = 0) :
    (Functor.const (Opens X)ᵒᵖ).map (AddCommGrpCat.ofHom ((coboundary ℚ p).toAddMonoidHom)) ≫
        ambientFixedCapPresheafMap X (p + 1) q (reassocChain ℚ p q z) =
      (-1 : ℤ) ^ (p + 1) • (ambientFixedCapPresheafMap X p (q + 1) z ≫
        ((subdivisionLimitSheafComplex X).d (q + 1) q).hom) := by
  apply NatTrans.ext
  funext U
  ext φ
  change Cochain ℚ (TopCat.toSSet.obj X) p at φ
  change subdivisionAmbientSectionMap X q U.unop 0
      (cap ℚ (p + 1) q (coboundary ℚ p φ) (reassocChain ℚ p q z)) =
    (-1 : ℤ) ^ (p + 1) • (((subdivisionLimitSheafComplex X).d (q + 1) q).hom.app U)
      (subdivisionAmbientSectionMap X (q + 1) U.unop 0 (cap ℚ p (q + 1) φ z))
  let f : ChainGroup ℚ (TopCat.toSSet.obj X) q →+
      ((subdivisionLimitSheafComplex X).X q).obj.obj U :=
    (subdivisionAmbientSectionMap X q U.unop 0).hom
  have h := congrArg f (fixedCycle_cap_coboundary X p q φ z hz)
  have hs := map_cap_sign f (p + 1) (boundary ℚ q (cap ℚ p (q + 1) φ z))
  have hb := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_boundary X q 0 U.unop)
    (cap ℚ p (q + 1) φ z)
  exact h.trans (hs.trans (congrArg (fun t => (-1 : ℤ) ^ (p + 1) • t) hb.symm))

#print axioms ambientFixedCapPresheafMap_coboundary
end HodgeLean.Foundations.RationalHomologyManifold
