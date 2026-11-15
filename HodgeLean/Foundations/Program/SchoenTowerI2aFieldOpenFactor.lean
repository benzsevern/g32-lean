import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The specified dominant point of a field factors uniquely and dominantly
through every nonempty actual open scheme chart.
Source: Hartshorne, Algebraic Geometry, II.3, generic points;
Mathlib, `IsOpenImmersion.lift` and `IsDominant.of_comp_of_isOpenImmersion`. -/
theorem s2v_i2a_dominant_field_point_open_factor
    {K : Type} [Field K] {X V : Scheme.{0}} [Nonempty V]
    (u : V ⟶ X) [IsOpenImmersion u]
    (η : Spec (CommRingCat.of K) ⟶ X) [IsDominant η] :
    ∃! ηV : Spec (CommRingCat.of K) ⟶ V, ηV ≫ u = η ∧ IsDominant ηV := by
  letI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨z, hz⟩ := η.denseRange.exists_mem_open u.isOpenEmbedding.isOpen_range
    (Set.range_nonempty u)
  have hrange : Set.range η ⊆ Set.range u := by
    rintro _ ⟨z', rfl⟩
    simpa only [Subsingleton.elim z' z] using hz
  let ηV := IsOpenImmersion.lift u η hrange
  have hηV : ηV ≫ u = η := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (ηV ≫ u) := hηV.symm ▸ inferInstance
  have hdom : IsDominant ηV := IsDominant.of_comp_of_isOpenImmersion ηV u
  refine ⟨ηV, ⟨hηV, hdom⟩, ?_⟩
  intro η' hη'
  apply (cancel_mono u).mp
  exact hη'.1.trans hηV.symm

end HodgeLean.Foundations.Program
