import HodgeLean.Foundations.Program.SchoenTowerI1aAffineDescent

import HodgeLean.Foundations.Program.SchoenTowerI1aAffineDescentLo
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_dominance_of_affine_restrictions
    {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    (h : ∀ U : Y.affineOpens, IsSchemeTheoreticallyDominant (f ∣_ U)) :
    IsSchemeTheoreticallyDominant f := by
  constructor
  apply le_antisymm _ bot_le
  intro U
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  apply le_of_eq
  apply (RingHom.injective_iff_ker_eq_bot _).mp
  haveI := h U
  have hinj := (f ∣_ U).app_injective ⊤
  change Function.Injective (f ∣_ U).appTop.hom at hinj
  rw [morphismRestrict_appTop] at hinj
  have hinj' : Function.Injective (f.app (U.1.ι ''ᵁ ⊤)).hom := by
    intro x y hxy
    apply hinj
    exact congrArg (X.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U.1 ⊤)).op).hom hxy
  rw [Scheme.Opens.ι_image_top] at hinj'
  exact hinj'


lemma s2v_i1ahi_surjective_opens_eq
    {X Y : Scheme} (f : X ⟶ Y) [Surjective f] {U V : Y.Opens}
    (h : f ⁻¹ᵁ U = f ⁻¹ᵁ V) : U = V := by
  apply TopologicalSpace.Opens.ext
  apply Set.preimage_injective.mpr f.surjective
  exact congrArg (fun W : X.Opens => (W : Set X)) h

lemma s2v_i1ahi_chart_restricted_square
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (Q : Scheme) (q : X.left ⟶ Q) [Surjective q]
    (O V : Q.Opens) (hi : ∀ g, q ⁻¹ᵁ O ≤ (a g).left ⁻¹ᵁ (q ⁻¹ᵁ O))
    (e : Spec ↧(s2v_i1a_chartInvariants X G a (q ⁻¹ᵁ O) hi) ≅ V.toScheme)
    (hpre : q ⁻¹ᵁ V = q ⁻¹ᵁ O)
    (hsq : (q ⁻¹ᵁ O).ι ≫ q =
      s2v_i1a_affineQuotientMap X G a (q ⁻¹ᵁ O) hi ≫ e.hom ≫ V.ι) :
    ∃ e' : Spec ↧(s2v_i1a_chartInvariants X G a (q ⁻¹ᵁ O) hi) ≅ O.toScheme,
      q ∣_ O = s2v_i1a_affineQuotientMap X G a (q ⁻¹ᵁ O) hi ≫ e'.hom := by
  have hVO : V = O := s2v_i1ahi_surjective_opens_eq q hpre
  subst V
  refine ⟨e, ?_⟩
  apply (cancel_mono O.ι).mp
  rw [morphismRestrict_ι, Category.assoc, hsq]

end HodgeLean.Foundations.Program
