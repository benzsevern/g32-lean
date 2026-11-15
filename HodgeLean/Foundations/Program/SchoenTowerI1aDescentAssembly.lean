import HodgeLean.Foundations.Program.SchoenTowerI1aEpimorphisms
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_local_factors_compatible
    {S Q T : Scheme} (q : S ⟶ Q) [Surjective q] [QuasiCompact q]
    [IsSchemeTheoreticallyDominant q] (f : S ⟶ T)
    (U V : Q.Opens) (u : U.toScheme ⟶ T) (v : V.toScheme ⟶ T)
    (hu : (q ∣_ U) ≫ u = (q ⁻¹ᵁ U).ι ≫ f)
    (hv : (q ∣_ V) ≫ v = (q ⁻¹ᵁ V).ι ≫ f) :
    Q.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ u =
      Q.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ v := by
  letI := s2v_i1ahi_restricted_scheme_epi q (U ⊓ V)
  apply (cancel_epi (q ∣_ (U ⊓ V))).mp
  rw [← Category.assoc, morphismRestrict_homOfLE, Category.assoc, hu,
    ← Category.assoc, Scheme.homOfLE_ι]
  rw [← Category.assoc, morphismRestrict_homOfLE, Category.assoc, hv,
    ← Category.assoc, Scheme.homOfLE_ι]

end HodgeLean.Foundations.Program
