import HodgeLean.Foundations.Program.SchoenCycleC2AffinePullbackHelpers

/-! # Naturality of the affine pullback presentation -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The affine pullback presentation commutes with every module morphism. -/
lemma unionConormal_affinePullback_naturality (S B : CommRingCat.{0}) (q : S ⟶ B)
    (K L : ModuleCat S) (E : K ⟶ L) :
    (Scheme.Modules.pullback (Spec.map q)).map ((tilde.functor S).map E) ≫
        (s2e_affine_pullback_tilde_iso S B q).hom.app L =
      (s2e_affine_pullback_tilde_iso S B q).hom.app K ≫
        (tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E) :=
  (s2e_affine_pullback_tilde_iso S B q).hom.naturality E

end HodgeLean.Foundations.Program.G32Native
