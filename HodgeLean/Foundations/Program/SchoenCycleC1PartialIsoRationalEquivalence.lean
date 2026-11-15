import HodgeLean.Foundations.Program.SchoenCycleC1OpenImmersionRationalEquivalence
import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericPoint
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackSquare
import Mathlib.AlgebraicGeometry.Birational.Birational

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A retained partial isomorphism over the original dominant morphism
makes its specified generic stalk pullback a field equivalence, retaining
every local stalk square of that morphism. -/
theorem s2e_c1_partial_iso_rational_equivalence
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (P : X.PartialIso Y)
    (hP : P.iso.hom ≫ P.target.ι = P.source.ι ≫ f) :
    let hg := s2e_c1_dominant_generic_point f
    let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    ∃ E : Y.functionField ≃+* X.functionField, E.toRingHom = φ ∧
      ∀ (p : X) (r : Y.presheaf.stalk (f p)),
        E (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
          algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r) := by
  letI : Nonempty P.source := P.dense_source.nonempty.to_subtype
  letI : Nonempty P.target := P.dense_target.nonempty.to_subtype
  let hg := s2e_c1_dominant_generic_point f
  let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    f.stalkMap (genericPoint X)).hom
  have hφ := s2e_c1_generic_stalk_map_local_square f hg
  obtain ⟨Es, hs⟩ := s2e_c1_open_immersion_rational_equivalence P.source.ι
  obtain ⟨Et, ht⟩ := s2e_c1_open_immersion_rational_equivalence P.target.ι
  obtain ⟨Ei, hi⟩ := s2e_c1_open_immersion_rational_equivalence P.iso.hom
  have hcomm := s2e_c1_rational_pullback_square P.source.ι f P.iso.hom P.target.ι hP.symm
    Es.toRingHom φ Ei.toRingHom Et.toRingHom hs hφ hi ht
  let E := (Et.trans Ei).trans Es.symm
  have hE (r : Y.functionField) : E r = φ r := by
    apply Es.injective
    change Es (Es.symm (Ei (Et r))) = Es (φ r)
    rw [Es.apply_symm_apply]
    exact (RingHom.congr_fun hcomm r).symm
  refine ⟨E, RingHom.ext hE, ?_⟩
  intro p r
  rw [hE]
  exact hφ p r

end HodgeLean.Foundations.Program
