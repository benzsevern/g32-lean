import HodgeLean.Foundations.Program.G32Native.QuaternionFramedOrbit
import HodgeLean.Blocks.Weil.RationalKernel

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
open HodgeBlocks HodgeBlocks.WeilAction
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The complex exterior span of a rational exterior subspace. -/
def complexSpan {n : ℕ} (U : Submodule ℚ (⋀[ℚ]^n V)) :
    Submodule ℂ (⋀[ℂ]^n (ℂ ⊗[ℚ] V)) :=
  Submodule.span ℂ (complexifyWedge n '' (U : Set (⋀[ℚ]^n V)))

/-- A complex span bound is equivalent to its rational generator bound. -/
theorem complexSpan_le_iff {n : ℕ} (U : Submodule ℚ (⋀[ℚ]^n V))
    (S : Submodule ℂ (⋀[ℂ]^n (ℂ ⊗[ℚ] V))) :
    complexSpan U ≤ S ↔ U ≤ (S.restrictScalars ℚ).comap (complexifyWedge n) := by
  constructor
  · intro h x hx
    exact h (Submodule.subset_span ⟨x,hx,rfl⟩)
  · intro h
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact h hx

/-- Extension of the exterior span is monotone. -/
theorem complexSpan_mono {n : ℕ} {U W : Submodule ℚ (⋀[ℚ]^n V)} (h : U ≤ W) :
    complexSpan U ≤ complexSpan W := by
  apply (complexSpan_le_iff _ _).mpr
  intro x hx
  exact Submodule.subset_span ⟨x,h hx,rfl⟩

/-- Complex exterior span preserves arbitrary sums of rational subspaces. -/
theorem complexSpan_iSup {n : ℕ} {I : Type*} (U : I → Submodule ℚ (⋀[ℚ]^n V)) :
    complexSpan (⨆ i, U i) = ⨆ i, complexSpan (U i) := by
  apply le_antisymm
  · apply (complexSpan_le_iff _ _).mpr
    apply iSup_le
    intro i
    exact (complexSpan_le_iff _ _).mp (le_iSup (fun i => complexSpan (U i)) i)
  · apply iSup_le
    intro i
    exact complexSpan_mono (le_iSup U i)

/-- Exterior span extension intertwines a rational action with its complexified action. -/
theorem complexSpan_map {n : ℕ} (U : Submodule ℚ (⋀[ℚ]^n V)) (f : Module.End ℚ V) :
    complexSpan (U.map (exteriorPower.map n f)) =
      (complexSpan U).map (exteriorPower.map n (f.baseChange ℂ)) := by
  rw [complexSpan, complexSpan, Submodule.map_span]
  apply congrArg (Submodule.span ℂ)
  ext z
  constructor
  · rintro ⟨_, ⟨x,hx,rfl⟩,rfl⟩
    exact ⟨complexifyWedge n x, ⟨x,hx,rfl⟩,
      (complexifyWedge_exteriorPower_map n f x).symm⟩
  · rintro ⟨_, ⟨x,hx,rfl⟩,rfl⟩
    exact ⟨exteriorPower.map n f x, ⟨x,hx,rfl⟩,
      complexifyWedge_exteriorPower_map n f x⟩

/-- The complex exterior span equals scalar extension transported through the exterior comparison. -/
theorem complexSpan_eq_map_baseChange {n : ℕ} (U : Submodule ℚ (⋀[ℚ]^n V)) :
    complexSpan U = (U.baseChange ℂ).map (exteriorPowerBaseChangeEquiv (V := V) n).toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  apply congrArg (Submodule.span ℂ)
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨1 ⊗ₜ[ℚ] x, ⟨x,hx,rfl⟩, exteriorPowerBaseChangeEquiv_tmul n x⟩
  · rintro ⟨_, ⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,(exteriorPowerBaseChangeEquiv_tmul n x).symm⟩

/-- Complexification of an exterior span preserves its rational dimension. -/
theorem complexSpan_finrank {n : ℕ} (U : Submodule ℚ (⋀[ℚ]^n V)) :
    Module.finrank ℂ (complexSpan U) = Module.finrank ℚ U := by
  rw [complexSpan_eq_map_baseChange]
  have h₁ : Module.finrank ℂ ((U.baseChange ℂ).map
      (exteriorPowerBaseChangeEquiv (V := V) n).toLinearMap) =
      Module.finrank ℂ (U.baseChange ℂ) :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (exteriorPowerBaseChangeEquiv (V := V) n).injective _).symm
  rw [h₁, ← LinearEquiv.finrank_eq (Submodule.toBaseChange.toLinearEquiv ℂ U),
    Module.finrank_baseChange]

/-- Rational exterior orbits extend to the actual complexified operator family. -/
theorem complexSpan_exteriorOrbit {n : ℕ} {I : Type*}
    (T : I → Module.End ℚ V) (U : Submodule ℚ (⋀[ℚ]^n V)) :
    complexSpan (exteriorOrbit T U) =
      exteriorOrbit (fun i => (T i).baseChange ℂ) (complexSpan U) := by
  rw [exteriorOrbit, complexSpan_iSup]
  simp only [complexSpan_map, exteriorOrbit]

#print axioms complexSpan_finrank
#print axioms complexSpan_exteriorOrbit
end HodgeLean.Foundations.Program.QuaternionGraph
