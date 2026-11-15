import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryLocusTransport
import Mathlib.AlgebraicGeometry.Noetherian
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryLocusRestriction

noncomputable section
open CategoryTheory TopologicalSpace
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

set_option backward.isDefEq.respectTransparency false in
theorem boundary_affine_flat_fiber_open {X Y : Scheme} [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] :
    IsOpen {y : Y | ∀ x : X, f x = y → (f.stalkMap x).hom.Flat} := by
  haveI : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let g := X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom
  have hg : IsOpen {y : Spec Γ(Y, ⊤) | ∀ x : Spec Γ(X, ⊤), g x = y →
      (g.stalkMap x).hom.Flat} := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective g
    haveI : IsFinite (Spec.map φ) := hφ ▸ inferInstanceAs (IsFinite g)
    rw [← hφ]
    exact boundary_spec_flat_fiber_open φ
  have hg' : IsOpen {y : Spec Γ(Y, ⊤) | ∀ x : X, (f ≫ Y.isoSpec.hom) x = y →
      ((f ≫ Y.isoSpec.hom).stalkMap x).hom.Flat} := by
    change IsOpen {y | ∀ x, (X.isoSpec.symm.hom ≫ (f ≫ Y.isoSpec.hom)) x = y →
      ((X.isoSpec.symm.hom ≫ (f ≫ Y.isoSpec.hom)).stalkMap x).hom.Flat} at hg
    rwa [boundary_flat_fiber_source_iso X.isoSpec.symm (f ≫ Y.isoSpec.hom)] at hg
  have hp := hg'.preimage Y.isoSpec.hom.continuous
  rwa [boundary_flat_fiber_target_iso f Y.isoSpec] at hp

set_option backward.isDefEq.respectTransparency false in
theorem boundary_finite_flat_fiber_open {X Y : Scheme} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] :
    IsOpen {y : Y | ∀ x : X, f x = y → (f.stalkMap x).hom.Flat} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (Opens.mem_top y)
  change Y.Opens at U
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have hpre : IsOpen (U.ι ⁻¹'
      {z : Y | ∀ x : X, f x = z → (f.stalkMap x).hom.Flat}) := by
    rw [boundary_flat_fiber_restrict]
    exact boundary_affine_flat_fiber_open (f ∣_ U)
  refine ⟨U.ι '' (U.ι ⁻¹'
    {z : Y | ∀ x : X, f x = z → (f.stalkMap x).hom.Flat}), ?_,
    U.ι.isOpenEmbedding.isOpenMap _ hpre, ?_⟩
  · rintro z ⟨u, hu, rfl⟩
    exact hu
  · exact ⟨⟨y, hyU⟩, hy, rfl⟩

theorem boundary_finite_nonflat_image_closed {X Y : Scheme} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] : IsClosed (f '' {x | ¬ (f.stalkMap x).hom.Flat}) := by
  have heq : f '' {x | ¬ (f.stalkMap x).hom.Flat} =
      {y : Y | ∀ x : X, f x = y → (f.stalkMap x).hom.Flat}ᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      exact hx (hy x rfl)
    · intro hy
      change ¬ (∀ x : X, f x = y → (f.stalkMap x).hom.Flat) at hy
      push_neg at hy
      obtain ⟨x, hx, hf⟩ := hy
      exact ⟨x, hf, hx⟩
  rw [heq]
  exact (boundary_finite_flat_fiber_open f).isClosed_compl

end AlgebraicGeometry.SingularCycles
