import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrameRestrictions

/-! # Actual native dual frame sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The native dual section taking value one on the original frame. -/
def pairedC3NativeDualFrameSection {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) : Γ(M.dual, U) :=
  (pairedC3NativeDualFrameEquiv hs).symm 1

/-- The actual unit-valued dual section is a frame on every smaller open. -/
theorem paired_c3_native_dual_frame {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) :
    IsFrameOn (pairedC3NativeDualFrameSection hs) U := by
  intro W hWU _
  let E : Γ(M.dual, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
    pairedC3NativeDualFrameEquiv ((hs.map (homOfLE hWU)).mono hWU)
  let q : Γ(M.dual, W) := M.dual.presheaf.map (homOfLE hWU).op (pairedC3NativeDualFrameSection hs)
  have he : E q = 1 := by
    have h := paired_c3_native_dual_frame_restrict hs hWU (pairedC3NativeDualFrameSection hs)
    change E q = X.presheaf.map (homOfLE hWU).op
      ((pairedC3NativeDualFrameEquiv hs) ((pairedC3NativeDualFrameEquiv hs).symm 1)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.trans (map_one _)
  have hr (r : Γ(X, W)) : E (r • q) = r := by
    calc
      E (r • q) = r • E q := E.map_smul r q
      _ = r := by rw [he, smul_eq_mul, mul_one]
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h := congrArg E hab
    exact (hr a).symm.trans (h.trans (hr b))
  · intro y
    refine ⟨E y, E.injective ?_⟩
    exact hr (E y)

#print axioms pairedC3NativeDualFrameSection
#print axioms paired_c3_native_dual_frame
end HodgeLean.Foundations.Program.G32Native
