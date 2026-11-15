import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachedCollarHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5TopHelpers

/-! Integral chains on attached collar deformations.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- A specified deformation retraction gives a homotopy equivalence on integral singular chains.
Source: Hatcher §2.1, homotopy invariance; Mathlib singularChainComplexFunctorObjMap. -/
def c1a5_retraction_chain_equiv {A B : TopCat.{0}}
    (i : A ⟶ B) (q : B ⟶ A) (hq : i ≫ q = 𝟙 A)
    (H : TopCat.Homotopy (𝟙 B) (q ≫ i)) :
    HomotopyEquiv
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj A)
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj B) := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  refine
    { hom := F.map i
      inv := F.map q
      homotopyHomInvId := Homotopy.ofEq ?_
      homotopyInvHomId := ?_ }
  · rw [← F.map_comp, hq, F.map_id]
  · have H' : TopCat.Homotopy (q ≫ i) (𝟙 B) := H.symm
    have h := H'.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
    change Homotopy (F.map (q ≫ i)) (F.map (𝟙 B)) at h
    rw [F.map_comp, F.map_id] at h
    exact h

example := @c1a5_retraction_chain_equiv

/-- Attaching a boundary collar preserves the integral singular homology of the base.
Source: Hatcher §2.1, homotopy invariance and the attached collar deformation. -/
lemma c1a5_attached_collar_chains_quasiIso {A B U : TopCat.{0}}
    (t : A ⟶ B) (j : A ⟶ U) (q : U ⟶ A) (hq : j ≫ q = 𝟙 A)
    (H : TopCat.Homotopy (𝟙 U) (q ≫ j))
    (hfixed : ∀ (s : unitInterval) (a : A), H (s, j a) = j a) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (pushout.inl t j)) :=
  (c1a5_retraction_chain_equiv (pushout.inl t j)
    (c1a5_attached_collar_retract t j q hq)
    (c1a5_attached_collar_retract_inl t j q hq)
    (c1a5_attached_collar_homotopy t j q hq H hfixed)).quasiIso_hom

end HodgeLean.Foundations.Program
