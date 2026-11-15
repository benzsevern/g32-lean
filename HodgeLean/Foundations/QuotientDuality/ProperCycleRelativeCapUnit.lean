import HodgeLean.Foundations.QuotientDuality.ProperCycleCapPairing

/-! # Actual degree-zero relative cap evaluation against the original unit -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluating the actual relative cap ending in degree zero against the original unit cochain recovers the original relative cochain.
Source: Hatcher, Algebraic Topology, sections 3.2 and 3.3, the cup unit and relative cap evaluation.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cap_unit_cochain
    (P : TopPair.{0}) (p : ℕ) (φ : RelativeCochain ℚ P p) :
    (unitCochain (R := ℚ) P.fst).comp (relativeCap ℚ P p 0 φ) = φ := by
  have h : relativeCapHom ℚ P p 0 φ ≫ ModuleCat.ofHom (unitCochain (R := ℚ) P.fst) =
      ModuleCat.ofHom φ := by
    apply Cofork.IsColimit.hom_ext (relativeChainProjectionComponentIsCokernelForCap ℚ P p)
    change (relativeChainProjection ℚ P).f p ≫
      (relativeCapHom ℚ P p 0 φ ≫ _) = (relativeChainProjection ℚ P).f p ≫ _
    calc
      _ = ModuleCat.ofHom (relativeCapLift ℚ P p 0 φ) ≫
          ModuleCat.ofHom (unitCochain (R := ℚ) P.fst) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun g => g ≫ ModuleCat.ofHom (unitCochain (R := ℚ) P.fst))
            (relativeChainProjection_relativeCapHom ℚ P p 0 φ))
      _ = _ := by
        apply ModuleCat.hom_ext
        ext c
        change cupCochain P.fst p 0 (relativeCochainToAbsolute ℚ P p φ)
          (unitCochain (R := ℚ) P.fst) c = relativeCochainToAbsolute ℚ P p φ c
        exact LinearMap.congr_fun (cupCochain_one P.fst p (relativeCochainToAbsolute ℚ P p φ)) c
  exact congrArg ModuleCat.Hom.hom h

end HodgeLean.Foundations.QuotientDuality
