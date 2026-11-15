import HodgeLean.Foundations.RationalHomologyManifold.CapSupport

/-! The actual rational submodule of ambient cochains vanishing near a specified point.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Ambient cochains whose values vanish on every simplex in some neighborhood of the specified point.
Source: Bredon, Sheaf Theory, second edition, VI.12; the local zero-cochain kernel in singular cochain sheafification.
HC no distance; AV milestone no distance.
-/
def localZeroCochains (X : TopCat.{0}) (x : X) (p : ℕ) :
    Submodule ℚ (Cochain ℚ (TopCat.toSSet.obj X) p) where
  carrier := {φ | ∃ U : Opens X, x ∈ U ∧ ∀ s,
    Set.range (X.toSSetObjEquiv _ s) ⊆ (U : Set X) → φ (chainOfSimplex ℚ s) = 0}
  zero_mem' := ⟨⊤, trivial, fun _ _ => rfl⟩
  add_mem' := by
    rintro φ ψ ⟨U, hxU, hU⟩ ⟨V, hxV, hV⟩
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun s hs => ?_⟩
    change φ (chainOfSimplex ℚ s) + ψ (chainOfSimplex ℚ s) = 0
    rw [hU s (fun y hy => (hs hy).1), hV s (fun y hy => (hs hy).2), add_zero]
  smul_mem' := by
    rintro r φ ⟨U, hxU, hU⟩
    refine ⟨U, hxU, fun s hs => ?_⟩
    change r • φ (chainOfSimplex ℚ s) = 0
    rw [hU s hs, smul_zero]

#print axioms localZeroCochains
/-- Vanishing on supported simplex generators is actual zero restriction of the cochain.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1; the free singular chain generators.
HC no distance; AV milestone no distance.
-/
theorem cochain_restrict_zero_of_simplex_zero (X : TopCat.{0}) (U : Set X) (p : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : ∀ s, Set.range (X.toSSetObjEquiv _ s) ⊆ U → φ (chainOfSimplex ℚ s) = 0) :
    cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) U).map) p φ = 0 := by
  let P := TopPair.ofSubset (X := X) U
  let r := cochainMap ℚ (TopCat.toSSet.map P.map) p φ
  have hr : ModuleCat.ofHom r = 0 := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hiota : (((TopCat.toSSet.obj P.snd).ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom a) =
        a • chainOfSimplex ℚ s := by
      rw [chainOfSimplex, ← map_smul]
      simp only [smul_eq_mul, mul_one]
    change r (((TopCat.toSSet.obj P.snd).ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom a) = 0
    rw [hiota, map_smul]
    change a • (cochainMap ℚ (TopCat.toSSet.map P.map) p φ (chainOfSimplex ℚ s)) = 0
    rw [cochainMap_apply, chainOfSimplex_map]
    have hz := hφ _ ((singularSimplex_subspace_image_iff X U p _).mp ⟨s, rfl⟩)
    exact (congrArg (fun v : ℚ => a • v) hz).trans (smul_zero a)
  exact congrArg ModuleCat.Hom.hom hr

#print axioms cochain_restrict_zero_of_simplex_zero
/-- The local zero-cochain submodule consists exactly of cochains with zero restriction on some neighborhood.
Source: Bredon, Sheaf Theory, second edition, VI.12; the singular cochain germ kernel.
HC no distance; AV milestone no distance.
-/
theorem mem_localZeroCochains_iff (X : TopCat.{0}) (x : X) (p : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p) :
    φ ∈ localZeroCochains X x p ↔ ∃ U : Opens X, x ∈ U ∧
      cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) (U : Set X)).map) p φ = 0 := by
  constructor
  · rintro ⟨U, hx, hU⟩
    exact ⟨U, hx, cochain_restrict_zero_of_simplex_zero X U p φ hU⟩
  · rintro ⟨U, hx, hU⟩
    exact ⟨U, hx, fun s hs => cochain_zero_on_supported_simplex X U p φ hU s hs⟩

#print axioms mem_localZeroCochains_iff
/-- Actual coboundary preserves the local zero-cochain submodule.
Source: Hatcher, Algebraic Topology, section 3.1; coboundary is a signed sum over simplex faces.
HC no distance; AV milestone no distance.
-/
theorem coboundary_mem_localZeroCochains (X : TopCat.{0}) (x : X) (p : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p) (hφ : φ ∈ localZeroCochains X x p) :
    coboundary ℚ p φ ∈ localZeroCochains X x (p + 1) := by
  obtain ⟨U, hx, hU⟩ := hφ
  refine ⟨U, hx, fun s hs => ?_⟩
  rw [coboundary_chainOfSimplex]
  apply Finset.sum_eq_zero
  intro i hi
  have hh : φ (chainOfSimplex ℚ ((TopCat.toSSet.obj X).δ i s)) = 0 :=
    hU _ (singularSimplex_map_support X U p (p + 1) (SimplexCategory.δ i) s hs)
  rw [hh, smul_zero]

#print axioms coboundary_mem_localZeroCochains
end HodgeLean.Foundations.RationalHomologyManifold
