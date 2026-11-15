import HodgeLean.Foundations.Program.SchoenTowerI1aGluedChartPreimages
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_finite_restriction_from_chart
    {S Q V R : Scheme} (q : S ⟶ Q) (j : V ⟶ S) [IsOpenImmersion j]
    (D : Q.Opens) (e : R ≅ D.toScheme) (p : V ⟶ R) [IsFinite p]
    (hsq : p ≫ e.hom ≫ D.ι = j ≫ q)
    (hrange : Set.range j = (q ⁻¹ᵁ D : Set S)) : IsFinite (q ∣_ D) := by
  let b := IsOpenImmersion.isoOfRangeEq j (q ⁻¹ᵁ D).ι
    (hrange.trans (Scheme.Opens.range_ι _).symm)
  have hb : b.hom ≫ (q ⁻¹ᵁ D).ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hbp : b.hom ≫ (q ∣_ D) = p ≫ e.hom := by
    apply (cancel_mono D.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb]
    exact hsq.symm
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) b.hom, hbp]
  infer_instance

lemma s2v_i1ahi_glued_source_finite
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (Q : Scheme)
    (ι : ∀ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1},
      (s2v_i1ahi_chartDiagram X G a).obj U ⟶ Q)
    (hi : ∀ U, IsOpenImmersion (ι U))
    (hj : ∀ z : Q, ∃ U p, ι U p = z)
    (q : X.left ⟶ Q)
    (hq : ∀ U, U.1.1.ι ≫ q = s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫ ι U)
    (hpre : ∀ U, q ⁻¹' Set.range (ι U) = (U.1.1 : Set X.left))
    (hfin : ∀ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1},
      IsFinite (s2v_i1a_affineQuotientMap X G a U.1.1 U.2)) : IsFinite q := by
  haveI (U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}) :
      IsOpenImmersion (ι U) := hi U
  have hcov : (⨆ U, (ι U).opensRange) = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨U, p, rfl⟩ := hj z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, p, rfl⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun U => (ι U).opensRange) hcov
  intro U
  letI := hfin U
  apply s2v_i1ahi_finite_restriction_from_chart q U.1.1.ι (ι U).opensRange
    (ι U).isoOpensRange (s2v_i1a_affineQuotientMap X G a U.1.1 U.2)
  · rw [Scheme.Hom.isoOpensRange_hom_ι, hq]
  · rw [Scheme.Opens.range_ι]
    exact (hpre U).symm

end HodgeLean.Foundations.Program
