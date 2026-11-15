import HodgeLean.Foundations.Program.SchoenTowerI1aChartDescent
import HodgeLean.Foundations.Program.SchoenTowerI1aOpenAssembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_factor_square_on_open
    {S Q V R T : Scheme} (q : S ⟶ Q) (j : V ⟶ S) [IsOpenImmersion j]
    (D : Q.Opens) (e : R ≅ D.toScheme) (p : V ⟶ R)
    (hsq : p ≫ e.hom ≫ D.ι = j ≫ q)
    (hrange : Set.range j = (q ⁻¹ᵁ D : Set S))
    (f : S ⟶ T) (v : R ⟶ T) (hv : p ≫ v = j ≫ f) :
    (q ∣_ D) ≫ e.inv ≫ v = (q ⁻¹ᵁ D).ι ≫ f := by
  let b := IsOpenImmersion.isoOfRangeEq j (q ⁻¹ᵁ D).ι
    (hrange.trans (Scheme.Opens.range_ι _).symm)
  have hb : b.hom ≫ (q ⁻¹ᵁ D).ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hbp : b.hom ≫ (q ∣_ D) = p ≫ e.hom := by
    apply (cancel_mono D.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb]
    exact hsq.symm
  apply (cancel_epi b.hom).mp
  rw [← Category.assoc b.hom (q ∣_ D), hbp]
  rw [Category.assoc p e.hom, Iso.hom_inv_id_assoc, ← Category.assoc b.hom, hb]
  exact hv

lemma s2v_i1ahi_affine_target_factor
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) [IsAffine T] (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f) :
    ∃! v : Spec ↧(s2v_i1a_chartInvariants X G a U hiU) ⟶ T,
      s2v_i1a_affineQuotientMap X G a U hiU ≫ v = f :=
  s2v_i1ahi_affine_factor_from_sections X.left U hU
    (s2v_i1a_chartInvariants X G a U hiU) T f
    (s2v_i1ahi_invariantSectionMap X G a U hiU T f hf) rfl

end HodgeLean.Foundations.Program
