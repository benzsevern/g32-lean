import HodgeLean.Foundations.Program.SchoenTowerOrbitRadical

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- Equal ideal stabilizers identify the stabilizers of the selected actual orbit indices,
with the same underlying element of the original group. -/
def s2t_orbitStabilizerEquiv {A B G : Type*} [CommRing A] [CommRing B] [Group G]
    [MulSemiringAction G A] [MulSemiringAction G B]
    (qA : Ideal A) (qB : Ideal B)
    (hstab : ∀ g : G, g • qA = qA ↔ g • qB = qB) :
    let iA : MulAction.orbit G qA := ⟨qA, MulAction.mem_orbit_self qA⟩
    let iB : MulAction.orbit G qB := ⟨qB, MulAction.mem_orbit_self qB⟩
    MulAction.stabilizer G iA ≃* MulAction.stabilizer G iB := by
  let iA : MulAction.orbit G qA := ⟨qA, MulAction.mem_orbit_self qA⟩
  let iB : MulAction.orbit G qB := ⟨qB, MulAction.mem_orbit_self qB⟩
  refine
    { toFun := fun h => ⟨h.val, ?_⟩
      invFun := fun h => ⟨h.val, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · apply Subtype.ext
    exact (hstab _).mp (congrArg (fun i : MulAction.orbit G qA => (i : Ideal A)) h.property)
  · apply Subtype.ext
    exact (hstab _).mpr (congrArg (fun i : MulAction.orbit G qB => (i : Ideal B)) h.property)
  · intro h
    apply Subtype.ext
    rfl
  · intro h
    apply Subtype.ext
    rfl
  · intro h k
    apply Subtype.ext
    rfl

end HodgeLean.Foundations.Program
