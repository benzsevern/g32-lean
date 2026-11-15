import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCap

/-! The three-degree morphism obtained by fixing the chain argument of cap.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Cap with a fixed cycle, with the adjacent signs required for commuting squares.
Source: Hatcher, Algebraic Topology, section 3.3, cap boundary formula.
HC no distance; AV milestone no distance.
-/
def fixedCycleCapWindow (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0) :
    ((SingularChainComplex ℚ X).sc' (p + 2) (p + 1) p).linearDual ⟶
      (SingularChainComplex ℚ X).sc' (q + 2) (q + 1) q := by
  let z₂ := reassocChain ℚ p (q + 1) z
  let z₃ := reassocChain ℚ (p + 1) q z₂
  refine
    { τ₁ := ModuleCat.ofHom ((-1 : ℚ) ^ (p + 1) • (capLinear ℚ p (q + 2)).flip z)
      τ₂ := ModuleCat.ofHom ((capLinear ℚ (p + 1) (q + 1)).flip z₂)
      τ₃ := ModuleCat.ofHom ((-1 : ℚ) ^ (p + 2) • (capLinear ℚ (p + 2) q).flip z₃)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    change boundary ℚ (q + 1) ((-1 : ℚ) ^ (p + 1) • cap ℚ p (q + 2) φ z) =
      cap ℚ (p + 1) (q + 1) (coboundary ℚ p φ) z₂
    rw [map_smul]
    exact (fixedCycle_cap_coboundary X p (q + 1) φ z hz).symm
  · refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    change boundary ℚ q (cap ℚ (p + 1) (q + 1) φ z₂) =
      (-1 : ℚ) ^ (p + 2) • cap ℚ (p + 2) q (coboundary ℚ (p + 1) φ) z₃
    have hz₂ : boundary ℚ (p + 1 + q) z₂ = 0 := fixedCycle_reassoc X p q z hz
    rw [fixedCycle_cap_coboundary X (p + 1) q φ z₂ hz₂, smul_smul,
      ← pow_add, (Even.add_self (p + 2)).neg_one_pow, one_smul]

#print axioms fixedCycleCapWindow
/-- The fixed-cycle morphism on the standard short-complex models.
Source: Hatcher, Algebraic Topology, section 3.3, cap on cochains and chains.
HC no distance; AV milestone no distance.
-/
def fixedCycleCapHom (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0) :
    ((SingularChainComplex ℚ X).sc (p + 1)).linearDual ⟶
      (SingularChainComplex ℚ X).sc (q + 1) :=
  let K := SingularChainComplex ℚ X
  let eP := K.isoSc' (p + 2) (p + 1) p
    (by rw [ChainComplex.prev]; omega) (ChainComplex.next_nat_succ p)
  let eQ := K.isoSc' (q + 2) (q + 1) q
    (by rw [ChainComplex.prev]; omega) (ChainComplex.next_nat_succ q)
  ShortComplex.linearDualMap eP.inv ≫ fixedCycleCapWindow X p q z hz ≫ eQ.inv

#print axioms fixedCycleCapHom
/-- The middle component retains the literal Alexander–Whitney cap formula.
Source: Hatcher, Algebraic Topology, section 3.3, the cap construction.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapHom_middle (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0) :
    (fixedCycleCapHom X p q z hz).τ₂ =
      ModuleCat.ofHom ((capLinear ℚ (p + 1) (q + 1)).flip
        (reassocChain ℚ p (q + 1) z)) := by
  simp only [fixedCycleCapHom, fixedCycleCapWindow, ShortComplex.linearDualMap,
    ShortComplex.comp_τ₂]
  apply ModuleCat.hom_ext
  ext φ
  rfl

#print axioms fixedCycleCapHom_middle
end HodgeLean.Foundations.RationalHomologyManifold
