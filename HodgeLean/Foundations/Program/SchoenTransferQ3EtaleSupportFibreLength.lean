import HodgeLean.Foundations.Program.SchoenTransferQ3SupportFibreMultiplicity
import HodgeLean.Foundations.Program.SchoenTransferQ3Generalizing

/-! Generic fibre multiplicity without a separate stalk-dimension input. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- The etale reduced-support map supplies the stalk dimension needed by
the unreduced generic-length comparison on one actual good open. -/
theorem s4_q3_etale_support_point_fibre_generic_multiplicity
    {X W D : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsIntegral D.left] [Smooth D.hom]
    (q : X ⟶ W) (x : W.left) (η : (ccm3_inverseIdeal q.left x).subscheme)
    (hη : closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme)
    (κ : (ccm3_inverseIdeal q.left x).subscheme ⟶ D.left) [IsFinite κ]
    {P : Scheme} [IsReduced P]
    (ψ : P ⟶ (ccm3_inverseIdeal q.left x).subscheme) [IsImmersion ψ]
    (hψ : IsOpenEmbedding ψ.base) [Etale (ψ ≫ κ)] :
    ∃ V : (ccm3_inverseIdeal q.left x).subscheme.Opens, η ∈ V ∧
      ∀ (p : P) (_ : ψ p ∈ V) (r : ℕ), Order.coheight (κ (ψ p)) = r →
        pointFibreLength κ (ψ p) =
          (genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2 : ℕ∞) := by
  obtain ⟨V, hηV, hV⟩ := s4_q3_support_point_fibre_generic_multiplicity q x η hη κ ψ hψ
  refine ⟨V, hηV, ?_⟩
  intro p hp r hr
  apply hV p hp r hr
  let K := (ccm3_inverseIdeal q.left x).subscheme
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
  rw [ringKrullDim_stalk_eq_coheight, IsOpenEmbedding.coheight_eq ψ hψ, hco, hr]
  exact WithBot.coe_natCast r

end HodgeLean.Foundations.Program
