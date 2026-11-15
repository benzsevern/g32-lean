import HodgeLean.Foundations.Program.SchoenInvariantRings

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Invariant maps from an affine scheme to an affine scheme factor uniquely through
its invariant spectrum. -/
theorem s2_affineQuotientDesc (R B G T : Type) [CommRing R] [CommRing B]
    [CommRing T] [Algebra R B] [Group G] [MulSemiringAction G B]
    [SMulCommClass G R B]
    (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of T))
    (hf : ∀ g : G, Spec.map (CommRingCat.ofHom
      (MulSemiringAction.toRingHom G B g)) ≫ f = f) :
    ∃! d : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶
        Spec (CommRingCat.of T),
      Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B G) B)) ≫ d = f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hφ (t : T) (g : G) : g • φ.hom t = φ.hom t := by
    have hg := hf g
    rw [← Spec.map_comp] at hg
    exact congrArg (fun k => k.hom t) (Spec.map_injective hg)
  let ψ : T →+* FixedPoints.subalgebra R B G := φ.hom.codRestrict _ hφ
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · dsimp only
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext t
    rfl
  · intro d hd
    obtain ⟨δ, rfl⟩ := Spec.map_surjective d
    rw [← Spec.map_comp] at hd
    apply congrArg Spec.map
    have hδ := Spec.map_injective hd
    ext t
    exact congrArg (fun k => k.hom t) hδ

/-- An injection into a domain induces injections on all spectrum stalks. -/
theorem s2_spec_stalkMap_injective (A B : Type) [CommRing A] [CommRing B]
    [IsDomain B] (φ : A →+* B) (hφ : Function.Injective φ)
    (x : PrimeSpectrum B) :
    Function.Injective ((Spec.map (CommRingCat.ofHom φ)).stalkMap x) := by
  change Function.Injective ((Spec.sheafedSpaceMap (CommRingCat.ofHom φ)).hom.stalkMap x)
  rw [← localRingHom_comp_stalkIso]
  have hx : x.asIdeal.IsPrime := x.isPrime
  have hi : Function.Injective
      (Localization.localRingHom (PrimeSpectrum.comap φ x).asIdeal x.asIdeal φ rfl) :=
    IsLocalization.map_injective_of_injective' _ B _ _ (by simp) hφ
  exact (StructureSheaf.stalkIso B x).injective.comp
    (hi.comp (StructureSheaf.stalkIso A (PrimeSpectrum.comap φ x)).symm.injective)

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine quotient of a domain is an epimorphism for arbitrary scheme targets. -/
theorem s2_affineQuotient_epi (R B G : Type) [CommRing R] [CommRing B]
    [IsDomain B] [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G R B] :
    Epi (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B G) B))) := by
  apply CategoryTheory.Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply CategoryTheory.Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _
    (s2_fixedAlgebra_spec_surjective R B G)
  intro x
  apply ConcreteCategory.mono_of_injective
  exact s2_spec_stalkMap_injective _ B _ Subtype.val_injective x

end HodgeLean.Foundations.Program
