import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs

/-! # Local transport of supported cohomology pairs

HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
namespace AlgebraicGeometry.SingularCycles

/-- A continuous map between neighbourhoods defines the actual supported map of pairs.
Source: Hatcher, Algebraic Topology, §2.1; maps of pairs. -/
def neighborhoodPullbackPairMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S : Set X) (T : Set Y) (hS : ∀ x, f x ∈ T → x ∈ S)
    (V : Set X) (N : Set Y) (hVN : ∀ x ∈ V, f x ∈ N) :
    neighborhoodSupportComplementPair V S ⟶ neighborhoodSupportComplementPair N T :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x => ⟨f x, hVN x x.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun x => ⟨⟨f x.1, hVN x.1 x.1.2⟩, fun hx => x.2 (hS x.1 hx)⟩, by fun_prop⟩)
    (by ext x; rfl)

/-- Neighbourhood pullback commutes with restriction from the ambient supported pair.
Source: Hatcher, Algebraic Topology, §3.1; functoriality of relative cohomology. -/
theorem neighborhoodPullbackPairMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S : Set X) (T : Set Y) (hS : ∀ x, f x ∈ T → x ∈ S)
    (V : Set X) (N : Set Y) (hVN : ∀ x ∈ V, f x ∈ N) :
    neighborhoodPullbackPairMap f S T hS V N hVN ≫ a3b4_neighborhoodPairMap N T =
      a3b4_neighborhoodPairMap V S ≫ a3b4_supportPairMap f S T hS := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    rfl
  · ext x
    rfl

/-- Local pullback preserves normal projection coclasses when normal coordinates agree.
Source: Hatcher, Algebraic Topology, §3.1; functoriality of the normal projection pullback. -/
theorem neighborhoodPullbackPairMap_normalCoclass {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S : Set X) (T : Set Y) (hS : ∀ x, f x ∈ T → x ∈ S)
    (V : Set X) (N : Set Y) (hVN : ∀ x ∈ V, f x ∈ N)
    (r k : ℕ)
    (E : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin k → ℂ)))
    (e : OpenPartialHomeomorph Y ((Fin r → ℂ) × (Fin k → ℂ)))
    (hE : ∀ x ∈ E.source, x ∈ S ↔ (E x).2 = 0)
    (he : ∀ x ∈ e.source, x ∈ T ↔ (e x).2 = 0)
    (hVE : V ⊆ E.source) (hNe : N ⊆ e.source)
    (heval : ∀ x ∈ V, E x = e (f x)) :
    relativeCohomologyMap ℚ (2 * k) (neighborhoodPullbackPairMap f S T hS V N hVN)
      (chartNormalProjectionCoclass (Fin r → ℂ) k e T he N hNe) =
      chartNormalProjectionCoclass (Fin r → ℂ) k E S hE V hVE := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 1
  congr 1
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Subtype.ext
    exact (congrArg Prod.snd (heval x.1.1 x.1.2)).symm
  · ext x
    exact (congrArg Prod.snd (heval x.1 x.2)).symm

end AlgebraicGeometry.SingularCycles
