import HodgeLean.Foundations.BundleThom.Defs

/-! # Maps of supported pairs on bundle neighbourhoods

All maps retain the inherited zero support. The target can be an immersion
pair in a singular ambient space.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace Bundle AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]

/-- A neighbourhood with the complement of its inherited zero support.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, tubular neighbourhoods. -/
def i1_neighbourhoodPair (U : Opens (TotalSpace (Fin k → ℂ) E)) : TopPair :=
  TopPair.ofSubset (X := TopCat.of U) {z | z.1.2 ≠ 0}

/-- Inclusion of a neighbourhood as a map of zero-complement pairs.
Source: Hatcher, Algebraic Topology, §3.1, relative naturality. -/
def i1_neighbourhoodInclusion (U : Opens (TotalSpace (Fin k → ℂ) E)) :
    i1_neighbourhoodPair k E U ⟶
      TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (fun _ h => h)

/-- A continuous support-preserving map supplies an actual relative cohomology map.
Source: Hatcher, Algebraic Topology, §3.1, maps of pairs. -/
def i1_neighbourhoodPairMap (U : Opens (TotalSpace (Fin k → ℂ) E))
    {X : TopCat} (Z : Set X) (f : C(U, X))
    (hf : ∀ z : U, z.1.2 ≠ 0 → f z ∉ Z) :
    i1_neighbourhoodPair k E U ⟶ TopPair.ofSubset (X := X) Zᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom f) hf

example (U : Opens (TotalSpace (Fin k → ℂ) E)) (z : U) (hz : z.1.2 ≠ 0) :
    (i1_neighbourhoodPair k E U).snd := ⟨z, hz⟩

example (U : Opens (TotalSpace (Fin k → ℂ) E)) (z : U) :
    (i1_neighbourhoodInclusion k E U).right z = z.1 := rfl

example (U : Opens (TotalSpace (Fin k → ℂ) E)) {X : TopCat} (Z : Set X)
    (f : C(U, X)) (hf : ∀ z : U, z.1.2 ≠ 0 → f z ∉ Z) (z : U) :
    (i1_neighbourhoodPairMap k E U Z f hf).right z = f z := rfl

end HodgeLean.Foundations.BundleThom
