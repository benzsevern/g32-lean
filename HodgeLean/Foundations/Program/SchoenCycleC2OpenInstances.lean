import HodgeLean.Foundations.Program.SchoenCycleC2OpenComponentHelpers
import HodgeLean.Adapters.NormalConeB4Defs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

instance s2e_openScheme_locallyOfFiniteType (W : Over (Spec ↧ℂ))
    [LocallyOfFiniteType W.hom] (U : W.left.Opens) :
    LocallyOfFiniteType (ComplexPoint.openScheme W U).hom := by
  change LocallyOfFiniteType (U.ι ≫ W.hom)
  infer_instance

instance s2e_openScheme_isSeparated (W : Over (Spec ↧ℂ))
    [IsSeparated W.hom] (U : W.left.Opens) :
    IsSeparated (ComplexPoint.openScheme W U).hom := by
  change IsSeparated (U.ι ≫ W.hom)
  infer_instance

instance s2e_openScheme_quasiCompact (W : Over (Spec ↧ℂ))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (U : W.left.Opens) :
    QuasiCompact (ComplexPoint.openScheme W U).hom := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : CompactSpace W.left := HodgeLean.Adapters.a3b4_compactSpace W.hom
  letI : IsNoetherian W.left := {}
  change QuasiCompact (U.ι ≫ W.hom)
  infer_instance

end HodgeLean.Foundations.Program
