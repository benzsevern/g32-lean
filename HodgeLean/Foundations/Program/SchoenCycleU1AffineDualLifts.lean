import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver
import HodgeLean.Foundations.Program.SchoenCycleU1DualTransport

/-! # Local algebra lifts from the scheme dual-number test -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The scheme dual-number test gives uniqueness of residue-valued algebra lifts
on every monomorphic affine chart over the specified base chart.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_affine_dual_lifts_unique
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (hsep : Function.Injective (fun u : s2e_u1_specOver (DualNumber ℂ) ⟶ X => u ≫ f))
    (R S K : Type) [CommRing R] [CommRing S] [CommRing K]
    [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S]
    [Algebra ℂ K] [Algebra R K] [Algebra S K]
    [IsScalarTower ℂ R K] [IsScalarTower R S K] [IsScalarTower ℂ S K]
    (e : K ≃ₐ[ℂ] ℂ)
    (i : s2e_u1_specOver S ⟶ X) [Mono i]
    (j : s2e_u1_specOver R ⟶ Y)
    (hcomm : i ≫ f = s2e_u1_specOverMap ((Algebra.ofId R S).restrictScalars ℂ) ≫ j) :
    Subsingleton (S →ₐ[R] DualNumber K) := by
  refine ⟨fun u v => ?_⟩
  let U := s2e_u1_specOverMap (u.restrictScalars ℂ)
  let V := s2e_u1_specOverMap (v.restrictScalars ℂ)
  let a := s2e_u1_specOverMap ((Algebra.ofId R S).restrictScalars ℂ)
  have hbase : U ≫ a = V ≫ a := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom u.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom v.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (u.comp_algebraMap.trans v.comp_algebraMap.symm)
  have hif : (U ≫ i) ≫ f = (V ≫ i) ≫ f := by
    simpa only [Category.assoc, hcomm] using congrArg (fun w => w ≫ j) hbase
  have hi : U ≫ i = V ≫ i := s2e_u1_dual_separation_transport X Y f hsep K e hif
  have hs := congrArg Over.Hom.left ((cancel_mono i).mp hi)
  change Spec.map (CommRingCat.ofHom u.toRingHom) =
    Spec.map (CommRingCat.ofHom v.toRingHom) at hs
  rw [Spec.map_inj] at hs
  apply AlgHom.ext
  intro x
  exact congrArg (fun g : CommRingCat.of S ⟶ CommRingCat.of (DualNumber K) => g.hom x) hs

end HodgeLean.Foundations.Program
