import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCap
import HodgeLean.Foundations.Singular.Cup

/-! Chain-level evaluation and unit formulas for the actual cap construction.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Evaluation of chain cap is the ordered Alexander–Whitney cochain product.
Source: Hatcher, Algebraic Topology, section 3.3, the cup-cap formula.
HC no distance; AV milestone no distance.
-/
theorem chain_cap_evaluation (X : TopCat.{0}) (p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p) (ψ : Cochain ℚ (TopCat.toSSet.obj X) q) :
    ψ.comp (cap ℚ p q φ) = HodgeLean.Foundations.Singular.cupCochain X p q φ ψ := by
  let L := ψ.comp (cap ℚ p q φ)
  let R := HodgeLean.Foundations.Singular.cupCochain X p q φ ψ
  have hcat : ModuleCat.ofHom L = ModuleCat.ofHom R := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hiota :
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a =
          a • chainOfSimplex ℚ σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change L (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a) =
      R (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a)
    rw [hiota, map_smul, map_smul]
    congr 1
  exact congrArg ModuleCat.Hom.hom hcat

#print axioms chain_cap_evaluation
/-- Chain cap by the unit is exactly the canonical degree identification.
Source: Hatcher, Algebraic Topology, section 3.3, the chain-level cap unit.
HC no distance; AV milestone no distance.
-/
theorem chain_cap_unit (X : TopCat.{0}) (q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (0 + q)) :
    cap ℚ 0 q (HodgeLean.Foundations.Singular.unitCochain X) z =
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq
        (Nat.zero_add q)).hom.hom z := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro ψ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have h₁ := LinearMap.congr_fun
    (chain_cap_evaluation X 0 q (HodgeLean.Foundations.Singular.unitCochain X) ψ) z
  have h₂ := LinearMap.congr_fun (HodgeLean.Foundations.Singular.one_cupCochain X q ψ) z
  exact h₁.trans h₂

#print axioms chain_cap_unit
end HodgeLean.Foundations.RationalHomologyManifold
