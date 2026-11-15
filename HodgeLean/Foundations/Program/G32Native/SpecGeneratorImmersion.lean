import HodgeLean.Foundations.Program.G32Native.AffineGeneratorImmersion

/-! Affine-space embeddings of spectra from algebra generators. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Algebra generators embed a spectrum into affine space over the coefficient spectrum. -/
theorem g32l4_spec_generator_closedImmersion {R A K : Type} [CommRing R] [CommRing A]
    [Algebra R A] (v : K → A) (hv : Algebra.adjoin R (Set.range v) = ⊤) :
    IsClosedImmersion (AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (fun k => (Scheme.ΓSpecIso (.of A)).inv.hom (v k))) := by
  letI : Algebra R Γ(Spec (.of A), ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap R A)).toAlgebra
  let e : A ≃ₐ[R] Γ(Spec (.of A), ⊤) := {
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  have hgen : Algebra.adjoin R (Set.range (fun k => e (v k))) = ⊤ := by
    have h := congrArg (Subalgebra.map e.toAlgHom) hv
    rw [AlgHom.map_adjoin, ← Set.range_comp', Algebra.map_top,
      (AlgHom.range_eq_top e.toAlgHom).mpr e.surjective] at h
    exact h
  have hcoeff (r : R) :
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop.hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom r) = algebraMap R Γ(Spec (.of A), ⊤) r := by
    have h := congrArg (fun f : CommRingCat.of R ⟶ Γ(Spec (.of A), ⊤) => f r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R A)))
    exact h.symm
  exact g32l4_affine_generator_closedImmersion _ (Scheme.ΓSpecIso (.of R)).inv.hom hcoeff _ hgen

end HodgeLean.Foundations.Program
