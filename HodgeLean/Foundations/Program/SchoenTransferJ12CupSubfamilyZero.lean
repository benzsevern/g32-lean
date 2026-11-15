import HodgeLean.Foundations.Program.SchoenTransferE1Proofs
import Mathlib.Logic.Equiv.Fintype

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- An ordered degree-one cup vanishes when an embedded pulled-back subfamily has zero cup.
Source: extension of finite injections to permutations, graded alternation and cup concatenation. -/
theorem s4_selected_cup_subfamily_zero
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (m n : ℕ) (hmn : m ≤ n) (e : Fin m → Fin n) (he : Function.Injective e)
    (f : T ⟶ Y) (w : Fin m → HQ Y 1) (v : Fin n → HQ T 1)
    (hv : ∀ i, v (e i) = homPullback f 1 (w i))
    (hw : (cupProductOf Y).cupMulti m w = 0) :
    (cupProductOf T).cupMulti n v = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE hmn) e (by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun x : Fin n => x.val) hij) he
  have hadd : m + (n - m) = n := Nat.add_sub_of_le hmn
  let b : Fin (n - m) → HQ T 1 := fun j => v (σ (Fin.cast hadd (Fin.natAdd m j)))
  have hz : (cupProductOf T).cupMulti n (v ∘ σ) = 0 := by
    rw [(cupProductOf T).cupMulti_append (n - m) b m
      (fun i => homPullback f 1 (w i)) n hadd (v ∘ σ)]
    · rw [← s4_e1_cupMulti_pullback, hw, map_zero, LinearMap.map_zero₂]
    · intro i
      have hi : Fin.cast hadd (Fin.castAdd (n - m) i) = Fin.castLE hmn i := by
        apply Fin.ext
        rfl
      change v (σ _) = _
      rw [hi, hσ i, hv i]
    · intro j
      rfl
  have hp := ((cupProductOf T).cupAlternating n).map_perm (v ∘ σ) σ.symm
  have hcomp : (v ∘ σ) ∘ σ.symm = v := by funext i; simp
  rw [hcomp] at hp
  change (cupProductOf T).cupMulti n v = (Equiv.Perm.sign σ.symm) • (cupProductOf T).cupMulti n (v ∘ σ) at hp
  rw [hz, smul_zero] at hp
  exact hp

#print axioms s4_selected_cup_subfamily_zero
end HodgeLean.Foundations.Program
