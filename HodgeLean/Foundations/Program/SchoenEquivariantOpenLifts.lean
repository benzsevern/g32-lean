import HodgeLean.Foundations.Program.SchoenEquivariantOpenRestrictions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restriction between matching invariant opens inside an equivariant open image
is an equivariant scheme isomorphism for the supplied restricted actions. -/
theorem s2_equivariantOpenImmersion_openLift
    {X Y : Scheme.{0}} (G : Type) [Group G]
    (ρX : G →* Aut X) (ρY : G →* Aut Y) (f : X ⟶ Y) [IsOpenImmersion f]
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f)
    (U : X.Opens) (V : Y.Opens) (hpre : f ⁻¹ᵁ V = U)
    (ρU : G →* Aut U.toScheme) (ρV : G →* Aut V.toScheme)
    (hU : ∀ g : G, U.ι ≫ (ρX g).asIso.hom = (ρU g).asIso.hom ≫ U.ι)
    (hV : ∀ g : G, V.ι ≫ (ρY g).asIso.hom = (ρV g).asIso.hom ≫ V.ι)
    (him : (V : Set Y) ⊆ Set.range f) :
    ∃ t : U.toScheme ⟶ V.toScheme, IsIso t ∧ t ≫ V.ι = U.ι ≫ f ∧
      ∀ g : G, t ≫ (ρV g).asIso.hom = (ρU g).asIso.hom ≫ t := by
  have hmap : Set.range (U.ι ≫ f) ⊆ Set.range V.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hu : u.1 ∈ f ⁻¹ᵁ V := hpre.symm ▸ u.property
    exact hu
  let t := IsOpenImmersion.lift V.ι (U.ι ≫ f) hmap
  have ht : t ≫ V.ι = U.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (t ≫ V.ι) := by rw [ht]; infer_instance
  haveI : IsOpenImmersion t := IsOpenImmersion.of_comp t V.ι
  have hsurj : Function.Surjective t := by
    intro v
    obtain ⟨x, hx⟩ := him v.property
    have hxU : x ∈ U := by
      rw [← hpre]
      change f x ∈ V
      rw [hx]
      exact v.property
    let u : U.toScheme := ⟨x, hxU⟩
    refine ⟨u, V.ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun m => m u) ht).trans hx
  haveI : Epi t.base := ConcreteCategory.epi_of_surjective _ hsurj
  haveI : IsIso t := IsOpenImmersion.isIso t
  refine ⟨t, inferInstance, ht, ?_⟩
  intro g
  apply (cancel_mono V.ι).mp
  calc
    (t ≫ (ρV g).asIso.hom) ≫ V.ι = t ≫ V.ι ≫ (ρY g).asIso.hom := by
      rw [Category.assoc, ← hV g]
    _ = U.ι ≫ f ≫ (ρY g).asIso.hom := by rw [← Category.assoc, ht, Category.assoc]
    _ = U.ι ≫ (ρX g).asIso.hom ≫ f := by rw [hf g]
    _ = (ρU g).asIso.hom ≫ U.ι ≫ f := by rw [← Category.assoc, hU g, Category.assoc]
    _ = ((ρU g).asIso.hom ≫ t) ≫ V.ι := by rw [Category.assoc, ht]

end HodgeLean.Foundations.Program
