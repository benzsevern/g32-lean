import HodgeLean.Foundations.Program.SchoenTowerL1aIdealPullback

/-! # Kernels under actual open restrictions

Implication from a morphism factoring through an open immersion to the
kernel ideal on that open. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A morphism factoring through an open immersion has the expected restricted kernel.
Source: Hartshorne, Algebraic Geometry, II.5, restriction of ideal sheaves. -/
theorem s2v_l1a_open_kernel
    {T X Y : Scheme} (f : T ⟶ X) (u : X ⟶ Y) [IsOpenImmersion u]
    [QuasiCompact (f ≫ u)] :
    (f ≫ u).ker.comap u = f.ker := by
  have H : IsPullback f (𝟙 T) u (f ≫ u) :=
    IsPullback.of_vert_isIso_mono ⟨by simp only [Category.id_comp]⟩
  apply Scheme.IdealSheafData.ext
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (f ≫ u) f (𝟙 T) u H W).symm

end HodgeLean.Foundations.Program
