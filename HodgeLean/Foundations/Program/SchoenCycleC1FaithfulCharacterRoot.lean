import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Primitive values of faithful finite scalar characters -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- A faithful character of a finite group in a domain takes a primitive
value of order equal to the entire group cardinality. -/
theorem s2e_c1_faithful_character_primitive_value
    {G k : Type*} [Group G] [Finite G] [CommRing k] [IsDomain k]
    (χ : G →* kˣ) (hχ : Function.Injective χ) :
    ∃ g : G, IsPrimitiveRoot (χ g : k) (Nat.card G) := by
  let f : G →* k := (Units.coeHom k).comp χ
  have hf : Function.Injective f := Units.val_injective.comp hχ
  letI : IsCyclic G := isCyclic_of_injective_ringHom f hf
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  refine ⟨g, IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  exact (orderOf_injective f hf g).trans hg

end HodgeLean.Foundations.Program
