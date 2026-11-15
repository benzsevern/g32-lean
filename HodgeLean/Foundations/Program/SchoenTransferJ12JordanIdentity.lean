import HodgeLean.Foundations.Program.SchoenTransferRetraction

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A rational operator space stable under Jordan products contains the identity when it contains an injective operator. -/
theorem s4_selected_identity_mem_jordan_submodule
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Submodule ℚ (Module.End ℚ V))
    (hJ : ∀ U ∈ S, ∀ W ∈ S, U.comp W + W.comp U ∈ S)
    (T : Module.End ℚ V) (hT : T ∈ S) (hinj : Function.Injective T) :
    LinearMap.id ∈ S := by
  let C : Submodule ℚ (Module.End ℚ V) :=
    { carrier := {U | T.comp U = U.comp T}
      zero_mem' := by simp only [Set.mem_setOf_eq, LinearMap.comp_zero, LinearMap.zero_comp]
      add_mem' := by
        intro U W hU hW
        change T.comp (U + W) = (U + W).comp T
        rw [LinearMap.comp_add, LinearMap.add_comp, hU, hW]
      smul_mem' := by
        intro a U hU
        change T.comp (a • U) = (a • U).comp T
        rw [LinearMap.comp_smul, LinearMap.smul_comp, hU] }
  have hTC : T ∈ C := rfl
  have hstable (U : Module.End ℚ V) (hU : U ∈ S ⊓ C) : T.comp U ∈ S ⊓ C := by
    have hcomm : T.comp U = U.comp T := hU.2
    constructor
    · have h := S.smul_mem (2 : ℚ)⁻¹ (hJ T hT U hU.1)
      rw [← hcomm] at h
      have he : (2 : ℚ)⁻¹ • (T.comp U + T.comp U) = T.comp U := by module
      rwa [he] at h
    · change T.comp (T.comp U) = (T.comp U).comp T
      calc
        T.comp (T.comp U) = T.comp (U.comp T) := congrArg (fun Z => T.comp Z) hcomm
        _ = (T.comp U).comp T := (LinearMap.comp_assoc T U T).symm
  obtain ⟨U, hU, hUid⟩ := s4_retraction_in_stable_submodule (S ⊓ C)
    LinearMap.id T ⟨hT, hTC⟩
    (fun U hU => by simpa only [LinearMap.comp_id] using hstable U hU)
    (by simpa only [LinearMap.comp_id] using hinj)
  rw [LinearMap.comp_id] at hUid
  rw [← hUid]
  exact hU.1

#print axioms s4_selected_identity_mem_jordan_submodule
end HodgeLean.Foundations.Program
