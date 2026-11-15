import HodgeLean.Foundations.Program.SchoenCycleMixedStabilizerPermutations
import HodgeLean.Foundations.Program.SchoenCyclePowerPointStabilizer

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The independent indexed block permutation group is the actual stabilizer of the retained mixed tuple.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_mixed_point_stabilizer_equiv
    (X : Over (Spec ↧ℂ)) (n b : ℕ) (x : ComplexPoint (g3_power X n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint X) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj X n (ι ⟨a, i⟩)) x = p a) :
    ((a : Fin b) → Equiv.Perm (Fin (m a))) ≃* s2e_powerPointStabilizer X n x := by
  let t := ι.permCongrHom.toMonoidHom.comp
    (Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a)))
  have hmem (ρ : (a : Fin b) → Equiv.Perm (Fin (m a))) : t ρ ∈ s2e_powerPointStabilizer X n x := by
    apply (s2e_mixed_tuple_stabilizer_iff_block_permutations X n b x m ι p hp hx (t ρ)).mpr
    refine ⟨ρ, rfl, ?_⟩
    intro ρ' hρ'
    apply Equiv.Perm.sigmaCongrRightHom_injective
    apply ι.permCongr.injective
    exact hρ'.symm
  let f : ((a : Fin b) → Equiv.Perm (Fin (m a))) →* s2e_powerPointStabilizer X n x :=
    { toFun := fun ρ => ⟨t ρ, hmem ρ⟩
      map_one' := Subtype.ext t.map_one
      map_mul' := fun ρ τ => Subtype.ext (t.map_mul ρ τ) }
  apply MulEquiv.ofBijective f
  constructor
  · intro ρ τ h
    apply Equiv.Perm.sigmaCongrRightHom_injective
    apply ι.permCongr.injective
    exact congrArg Subtype.val h
  · intro σ
    obtain ⟨ρ, hρ, _⟩ :=
      (s2e_mixed_tuple_stabilizer_iff_block_permutations X n b x m ι p hp hx σ.val).mp σ.property
    exact ⟨ρ, Subtype.ext hρ.symm⟩

end HodgeLean.Foundations.Program
