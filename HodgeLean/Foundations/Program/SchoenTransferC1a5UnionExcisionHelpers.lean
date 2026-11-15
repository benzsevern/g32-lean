import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeHelpers
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! Relative integral chains for a union of singular subcomplexes.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- Replacing an ambient complex by a union comparison gives excision from the other member.
Source: Hatcher §2.1, Theorem 2.20, small-chain quotient argument;
Mathlib Subcomplex.BicartSq.isPushout. -/
lemma c1a5_union_relative_excision {X : SSet.{0}} (A B : X.Subcomplex)
    (h : QuasiIso (c1a5Chains.map (A ⊔ B).ι)) :
    QuasiIso (c1a5RelativeMap c1a5Chains
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) A.ι
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) B.ι (by rfl)) := by
  let f := SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)
  let g := SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)
  let a := SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)
  let b := SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)
  let u := c1a5RelativeMap c1a5Chains f g a b (by rfl)
  have hu : IsIso u := by
    exact isIso_cokernel_map_of_isPushout
      ((SSet.Subcomplex.BicartSq.isPushout
        (show SSet.Subcomplex.BicartSq (A ⊓ B) B A (A ⊔ B) from
          { sup_eq := sup_comm _ _, inf_eq := inf_comm _ _ })).map c1a5Chains)
  let v := cokernel.map (c1a5Chains.map g) (c1a5Chains.map A.ι)
    (𝟙 (c1a5Chains.obj (A : SSet))) (c1a5Chains.map (A ⊔ B).ι)
    (by rw [← c1a5Chains.map_comp]; rfl)
  have hv : QuasiIso v := by
    have := c1a5_chains_map_mono g
    have := c1a5_chains_map_mono A.ι
    exact c1a5_cokernel_comparison _ _ _ _ _ inferInstance h
  have huv : QuasiIso (u ≫ v) := by
    have := hu
    have := hv
    infer_instance
  have he : u ≫ v = c1a5RelativeMap c1a5Chains f A.ι a B.ι (by rfl) := by
    apply (cancel_epi (cokernel.π (c1a5Chains.map f))).1
    simp only [u, v, c1a5RelativeMap, cokernel.map, cokernel.π_desc_assoc,
      cokernel.π_desc, Category.assoc, Category.id_comp]
    rw [← Category.assoc, ← c1a5Chains.map_comp]
    rfl
  rwa [he] at huv

end HodgeLean.Foundations.Program
