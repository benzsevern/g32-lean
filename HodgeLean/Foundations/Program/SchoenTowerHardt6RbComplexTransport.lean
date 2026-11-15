import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineLifts
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceTransport
import Mathlib.Topology.Homeomorph.Lemmas

/-! Finite geometric complexes and their actual carrier maps under linear coordinate equivalences. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_complex_linear_transport {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (e : E ≃L[ℝ] F) :
    ∃ L : Geometry.SimplicialComplex ℝ F,
      L.faces = (fun s : Finset E => s.image e) '' K.faces ∧
      L.faces.Finite ∧ L.space = e '' K.space ∧
      ∃ k : K.space ≃ₜ L.space, ∀ x, (k x).val = e x.val := by
  obtain ⟨L, hfaces, hfinite, hspace⟩ :=
    s2v_hardt6rb_affine_lift_complex K hK e.toLinearEquiv.toAffineEquiv.toAffineMap e.injective
  let k : K.space ≃ₜ L.space :=
    (e.toHomeomorph.image K.space).trans (Homeomorph.setCongr hspace.symm)
  exact ⟨L, hfaces, hfinite, hspace, k, fun _ => rfl⟩

end HodgeLean.Foundations.Program
