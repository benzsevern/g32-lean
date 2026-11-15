import HodgeLean.Foundations.Program.SchoenTransferQ3SliceLengths
import HodgeLean.Foundations.Program.SchoenTransferQ3NilpotentParameters
import HodgeLean.Foundations.Program.SchoenTransferQ3ReducedPieceStalk
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreePointLength

/-! Unreduced point-fibre lengths on the etale reduced-support locus. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology IsLocalRing
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- On a generic good open, an etale reduced-support map identifies the
actual point-fibre length with the original inverse-component multiplicity. -/
theorem s4_q3_support_point_fibre_generic_multiplicity
    {X W D : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsIntegral D.left] [Smooth D.hom]
    (q : X ⟶ W) (x : W.left) (η : (ccm3_inverseIdeal q.left x).subscheme)
    (hη : closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme)
    (κ : (ccm3_inverseIdeal q.left x).subscheme ⟶ D.left)
    {P : Scheme} [IsReduced P]
    (ψ : P ⟶ (ccm3_inverseIdeal q.left x).subscheme) [IsImmersion ψ]
    (hψ : IsOpenEmbedding ψ.base) [Etale (ψ ≫ κ)] :
    ∃ V : (ccm3_inverseIdeal q.left x).subscheme.Opens, η ∈ V ∧
      ∀ (p : P) (_ : ψ p ∈ V) (r : ℕ),
        Order.coheight (κ (ψ p)) = r →
        ringKrullDim ((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk (ψ p)) = r →
        pointFibreLength κ (ψ p) =
          (genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2 : ℕ∞) := by
  obtain ⟨V, hηV, hV⟩ := s4_q3_inverse_component_regular_slice_length q x η hη
  refine ⟨V, hηV, ?_⟩
  intro p hp r hr hdim
  let K := (ccm3_inverseIdeal q.left x).subscheme
  let C : Over (Spec ↧ℂ) := Over.mk (ψ ≫ κ ≫ D.hom)
  let f : C ⟶ D := Over.homMk (ψ ≫ κ) (Category.assoc ψ κ D.hom)
  letI : Etale f.left := inferInstanceAs (Etale (ψ ≫ κ))
  obtain ⟨rs, hlen, hgen, _, _, hgenP⟩ :=
    s4_q3_etale_support_shared_parameters f p r hr
  let a := (κ.stalkMap (ψ p)).hom
  let b := (ψ.stalkMap p).hom
  have hb : Function.Surjective b := ψ.stalkMap_surjective p
  have hker : RingHom.ker b = nilradical (K.presheaf.stalk (ψ p)) :=
    s4_q3_reduced_open_piece_stalk_kernel ψ hψ p
  have hcomp : b.comp a = (f.left.stalkMap p).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp ψ κ p).symm
  have hgen' : Ideal.ofList (rs.map (b.comp a)) =
      maximalIdeal (P.presheaf.stalk p) := by rw [hcomp]; exact hgenP
  have hnil := s4_q3_parameters_generate_mod_nilradical a b hb hker rs hgen'
  have hlength := (hV (ψ p) hp (rs.map a) (by rw [List.length_map, hlen]; exact hdim) hnil).1
  have hideal : Ideal.ofList (rs.map a) =
      (maximalIdeal (D.left.presheaf.stalk (κ (ψ p)))).map a := by
    rw [← Ideal.map_ofList]
    exact congrArg (Ideal.map a) hgen
  rw [hideal] at hlength
  exact hlength

end HodgeLean.Foundations.Program
