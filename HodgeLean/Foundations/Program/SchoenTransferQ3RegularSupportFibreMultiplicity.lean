import HodgeLean.Foundations.Program.SchoenTransferQ3LocalSupportParameters
import HodgeLean.Foundations.Program.SchoenTransferQ3EtaleSupportFibreLength

/-! Retained generic multiplicity at regular points of a possibly singular support. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology IsLocalRing
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- A regular target stalk and an actual etale reduced piece suffice to
compute the unreduced generic multiplicity on one generic support open. -/
theorem s4_q3_regular_support_point_fibre_generic_multiplicity
    {X W : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (q : X ⟶ W) (x : W.left) (η : (ccm3_inverseIdeal q.left x).subscheme)
    (hη : closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme)
    {D : Scheme.{0}} [IsLocallyNoetherian D]
    (κ : (ccm3_inverseIdeal q.left x).subscheme ⟶ D) [IsFinite κ]
    {P : Scheme} [IsReduced P]
    (ψ : P ⟶ (ccm3_inverseIdeal q.left x).subscheme) [IsImmersion ψ]
    (hψ : IsOpenEmbedding ψ.base) [Etale (ψ ≫ κ)] :
    ∃ V : (ccm3_inverseIdeal q.left x).subscheme.Opens, η ∈ V ∧
      ∀ (p : P), ψ p ∈ V → ∀ (r : ℕ), Order.coheight (κ (ψ p)) = r →
        IsRegularLocalRing (D.presheaf.stalk (κ (ψ p))) →
        pointFibreLength κ (ψ p) =
          (genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2 : ℕ∞) := by
  obtain ⟨V, hηV, hV⟩ := s4_q3_inverse_component_regular_slice_length q x η hη
  refine ⟨V, hηV, ?_⟩
  intro p hp r hr hregular
  letI : IsRegularLocalRing (D.presheaf.stalk ((ψ ≫ κ) p)) := by
    change IsRegularLocalRing (D.presheaf.stalk (κ (ψ p)))
    exact hregular
  obtain ⟨rs, hlen, hgen, _, _, hgenP⟩ :=
    s4_q3_etale_regular_support_stalk_parameters (ψ ≫ κ) p r hr
  let K := (ccm3_inverseIdeal q.left x).subscheme
  let a := (κ.stalkMap (ψ p)).hom
  let b := (ψ.stalkMap p).hom
  have hb : Function.Surjective b := ψ.stalkMap_surjective p
  have hker : RingHom.ker b = nilradical (K.presheaf.stalk (ψ p)) :=
    s4_q3_reduced_open_piece_stalk_kernel ψ hψ p
  have hcomp : b.comp a = ((ψ ≫ κ).stalkMap p).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp ψ κ p).symm
  have hgen' : Ideal.ofList (rs.map (b.comp a)) = maximalIdeal (P.presheaf.stalk p) := by
    rw [hcomp]; exact hgenP
  have hnil := s4_q3_parameters_generate_mod_nilradical a b hb hker rs hgen'
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : NoetherianSpace K :=
    (ccm3_inverseIdeal q.left x).subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace P := hψ.isEmbedding.isInducing.noetherianSpace
  letI : IsLocallyNoetherian K :=
    LocallyOfFiniteType.isLocallyNoetherian (ccm3_inverseIdeal q.left x).subschemeι
  letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian ψ
  letI : IsNoetherian P := {}
  have hco := s4_q3_coheight_eq_of_open_quasiFinite (ψ ≫ κ) (ψ ≫ κ).isOpenMap p
  change Order.coheight p = Order.coheight (κ (ψ p)) at hco
  have hdim : ringKrullDim (K.presheaf.stalk (ψ p)) = (rs.map a).length := by
    rw [ringKrullDim_stalk_eq_coheight, IsOpenEmbedding.coheight_eq ψ hψ, hco, hr,
      List.length_map, hlen]
    exact WithBot.coe_natCast r
  have hlength := (hV (ψ p) hp (rs.map a) hdim hnil).1
  have hideal : Ideal.ofList (rs.map a) =
      (maximalIdeal (D.presheaf.stalk (κ (ψ p)))).map a := by
    rw [← Ideal.map_ofList]
    exact congrArg (Ideal.map a) hgen
  rw [hideal] at hlength
  exact hlength

end HodgeLean.Foundations.Program
