import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import HodgeLean.Foundations.Program.SchoenCycleAdicIdealKernel
import HodgeLean.Foundations.Program.SchoenCycleAdicStalkMap
import HodgeLean.Foundations.Program.SchoenCycleAffineSingletonFiber

/-! # Affine image kernels and actual adic stalk maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Over a singleton fiber at a closed point, vanishing under the actual adic
stalk map detects the extension of the affine section-map kernel.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_singleton_fiber_adic_stalk_kernel
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (x : X)
    (hclosed : IsClosed ({f x} : Set Y)) (hfiber : f ⁻¹' {f x} = {x})
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    let P := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
    ∃ hd : P.map (Y.presheaf.germ U (f x) hx).hom ≤
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)),
      ∀ z : AdicCompletion P Γ(Y, U),
        s2e_adic_stalkMap f x
          (s2e_adic_ring_map _ _ (Y.presheaf.germ U (f x) hx).hom hd z) = 0 ↔
        z ∈ (RingHom.ker (f.app U).hom).map
          (algebraMap Γ(Y, U) (AdicCompletion P Γ(Y, U))) := by
  intro P
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := f.finite_app U hU
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hd : P.map (Y.presheaf.germ U (f x) hx).hom ≤
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) :=
    (s2e_affine_germ_map_point_ideal Y U hU (f x) hx).le
  obtain ⟨hu, hb⟩ := s2e_affine_singleton_fiber_adic_map_bijective f x hclosed hfiber U hU hx
  refine ⟨hd, fun z => ?_⟩
  rw [s2e_adic_stalkMap_germ f x U hx P hd hu z]
  rw [map_eq_zero_iff _ hb.injective]
  have hk := s2e_adic_algebraMap_kernel (S := S) P
  change z ∈ RingHom.ker (s2e_adic_ring_map P (P.map (algebraMap R S))
    (algebraMap R S) le_rfl) ↔ _
  rw [hk]
  rfl

#print axioms s2e_singleton_fiber_adic_stalk_kernel
/-- The actual adic stalk kernel over a singleton fiber is the extension of
the affine image ideal localized by the actual germ map.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_singleton_fiber_adic_stalk_kernel_ideal
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (x : X)
    (hclosed : IsClosed ({f x} : Set Y)) (hfiber : f ⁻¹' {f x} = {x})
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    RingHom.ker (s2e_adic_stalkMap f x) =
      ((RingHom.ker (f.app U).hom).map (Y.presheaf.germ U (f x) hx).hom).map
        (algebraMap (Y.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
            (Y.presheaf.stalk (f x)))) := by
  let P := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
  let D := Y.presheaf.stalk (f x)
  let J := (RingHom.ker (f.app U).hom).map (algebraMap Γ(Y, U) (AdicCompletion P Γ(Y, U)))
  obtain ⟨hd, hz⟩ := s2e_singleton_fiber_adic_stalk_kernel f x hclosed hfiber U hU hx
  let g := s2e_adic_ring_map P (IsLocalRing.maximalIdeal D)
    (Y.presheaf.germ U (f x) hx).hom hd
  have hg : Function.Bijective g := s2e_affine_germ_adic_map_bijective Y U hU (f x) hx hclosed
  have hm : ((RingHom.ker (f.app U).hom).map (Y.presheaf.germ U (f x) hx).hom).map
      (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D)) = J.map g := by
    dsimp only [J]
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  rw [hm]
  apply Ideal.comap_injective_of_surjective g hg.surjective
  rw [Ideal.comap_map_of_bijective g hg]
  ext z
  exact hz z

#print axioms s2e_singleton_fiber_adic_stalk_kernel_ideal
/-- Over a singleton fiber, the actual algebraic stalk kernel is the affine
image ideal extended by the actual germ map.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_singleton_fiber_stalk_kernel
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (x : X)
    (hclosed : IsClosed ({f x} : Set Y)) (hfiber : f ⁻¹' {f x} = {x})
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    RingHom.ker (f.stalkMap x).hom =
      (RingHom.ker (f.app U).hom).map (Y.presheaf.germ U (f x) hx).hom := by
  let D := Y.presheaf.stalk (f x)
  let A := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let E := X.presheaf.stalk x
  letI : IsNoetherianRing D := inferInstanceAs (IsNoetherianRing (Y.presheaf.stalk (f x)))
  letI : IsNoetherianRing E := inferInstanceAs (IsNoetherianRing (X.presheaf.stalk x))
  letI : Module.FaithfullyFlat D A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Module.FaithfullyFlat E (AdicCompletion (IsLocalRing.maximalIdeal E) E) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have he : RingHom.ker (f.stalkMap x).hom =
      (RingHom.ker (s2e_adic_stalkMap f x)).comap (algebraMap D A) := by
    ext r
    change (f.stalkMap x).hom r = 0 ↔
      s2e_adic_stalkMap f x (AdicCompletion.of (IsLocalRing.maximalIdeal D) D r) = 0
    unfold s2e_adic_stalkMap
    rw [s2e_adic_ring_map_of]
    exact (map_eq_zero_iff (algebraMap E (AdicCompletion (IsLocalRing.maximalIdeal E) E))
      (FaithfulSMul.algebraMap_injective E _)).symm
  rw [he, s2e_singleton_fiber_adic_stalk_kernel_ideal f x hclosed hfiber U hU hx]
  exact Ideal.comap_map_eq_self_of_faithfullyFlat _

#print axioms s2e_singleton_fiber_stalk_kernel
/-- For a finite morphism with singleton closed fiber, the actual adic
stalk kernel is the extension of the actual algebraic stalk kernel.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_singleton_fiber_adic_kernel_eq_map
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (x : X)
    (hclosed : IsClosed ({f x} : Set Y)) (hfiber : f ⁻¹' {f x} = {x}) :
    RingHom.ker (s2e_adic_stalkMap f x) =
      (RingHom.ker (f.stalkMap x).hom).map
        (algebraMap (Y.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
            (Y.presheaf.stalk (f x)))) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  rw [s2e_singleton_fiber_stalk_kernel f x hclosed hfiber U hU hx]
  exact s2e_singleton_fiber_adic_stalk_kernel_ideal f x hclosed hfiber U hU hx

#print axioms s2e_singleton_fiber_adic_kernel_eq_map
end HodgeLean.Foundations.Program
