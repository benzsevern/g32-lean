import HodgeLean.Adapters.AbelianHomPullback
import Mathlib.RingTheory.Flat.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Injective abelian pullback reflects the holomorphic degree-one summand. -/
theorem s4_selected_holomorphic_reflection
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ X) [IsMonHom f] (hf : Function.Injective (homPullback f 1)) :
    (complexHolomorphicH1 Y).comap ((homPullback f 1).baseChange ℂ) ≤
      complexHolomorphicH1 X := by
  let F := (homPullback f 1).baseChange ℂ
  have hi : Function.Injective F :=
    Module.Flat.lTensor_preserves_injective_linearMap (homPullback f 1) hf
  intro v hv
  obtain ⟨u, hu, w, hw, huv⟩ := Submodule.mem_sup.mp
    (show v ∈ complexHolomorphicH1 X ⊔ complexAntiholomorphicH1 X by
      rw [(spec_complexH1_split X).1]
      trivial)
  have hFu : F u ∈ complexHolomorphicH1 Y :=
    (spec_homPullback_hodge f).1 (Submodule.mem_map_of_mem hu)
  have hFwA : F w ∈ complexAntiholomorphicH1 Y :=
    (spec_homPullback_hodge f).2 (Submodule.mem_map_of_mem hw)
  have hFwH : F w ∈ complexHolomorphicH1 Y := by
    have he : F w = F v - F u := by
      rw [← huv, map_add]
      abel
    rw [he]
    exact Submodule.sub_mem _ hv hFu
  have hzero : F w = 0 :=
    (Submodule.disjoint_def.mp (spec_complexH1_split Y).2) (F w) hFwH hFwA
  have hw0 : w = 0 := hi (hzero.trans (map_zero F).symm)
  rw [← huv, hw0, add_zero]
  exact hu

/-- An injective abelian pullback square forces its rational upper map to preserve H1 types. -/
theorem s4_selected_abelian_square_holomorphic
    (B D P : Over (Spec ↧ℂ)) [GrpObj B] [GrpObj D] [GrpObj P]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral D.left] [Smooth D.hom] [IsProjective D.hom]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (f : D ⟶ B) [IsMonHom f] (g : D ⟶ P) [IsMonHom g]
    (hf : Function.Injective (homPullback f 1))
    (T : HQ P 1 →ₗ[ℚ] HQ B 1)
    (hsq : (homPullback f 1).comp T = homPullback g 1) :
    (complexHolomorphicH1 P).map (T.baseChange ℂ) ≤ complexHolomorphicH1 B := by
  rintro _ ⟨v, hv, rfl⟩
  apply s4_selected_holomorphic_reflection B D f hf
  change (homPullback f 1).baseChange ℂ (T.baseChange ℂ v) ∈ complexHolomorphicH1 D
  have he := congrArg (LinearMap.baseChange ℂ) hsq
  rw [LinearMap.baseChange_comp] at he
  rw [← LinearMap.comp_apply, he]
  exact (spec_homPullback_hodge g).1 (Submodule.mem_map_of_mem hv)

#print axioms s4_selected_abelian_square_holomorphic

#print axioms s4_selected_holomorphic_reflection

end HodgeLean.Foundations.Program
