import HodgeLean.Foundations.Program.SchoenTransferC1a5SubspaceExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5ExcisionCubeHelpers

/-! Transporting relative open-cover comparisons through actual continuous maps.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Restriction of a specified continuous map between specified subspaces.
Source: the subspace topology. -/
def c1a5_map_subspace {X Y : TopCat.{0}} (f : X ⟶ Y) (U : Set X) (V : Set Y)
    (h : ∀ x ∈ U, f x ∈ V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x.val, h x.val x.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

example {X Y : TopCat.{0}} (f : X ⟶ Y) :=
  c1a5_map_subspace f Set.univ Set.univ (by intros; trivial)

/-- Comparisons on a cover member and its overlap transport relative homology across the ambient map.
Source: Hatcher §2.1, Theorem 2.20, naturality of the two relative excision maps. -/
lemma c1a5_open_cover_relative_transport {X Y : TopCat.{0}} (f : X ⟶ Y)
    (U V : Set X) (U' V' : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hX : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hY : U' ∪ V' = Set.univ)
    (hfU : ∀ x ∈ U, f x ∈ U') (hfV : ∀ x ∈ V, f x ∈ V')
    (hi : QuasiIso (c1a5Chains.map (TopCat.toSSet.map
      (c1a5_map_subspace f (U ∩ V) (U' ∩ V')
        (fun x hx ↦ ⟨hfU x hx.1, hfV x hx.2⟩)))))
    (hv : QuasiIso (c1a5Chains.map (TopCat.toSSet.map
      (c1a5_map_subspace f V V' hfV)))) :
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (topologicalSubsetInclusion X U))
      (TopCat.toSSet.map (topologicalSubsetInclusion Y U'))
      (TopCat.toSSet.map (c1a5_map_subspace f U U' hfU))
      (TopCat.toSSet.map f) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl)) := by
  let p := TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_right : U ∩ V ⊆ V))
  let q := TopCat.toSSet.map (topologicalSubsetInclusion X U)
  let a := TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_left : U ∩ V ⊆ U))
  let b := TopCat.toSSet.map (topologicalSubsetInclusion X V)
  let p' := TopCat.toSSet.map (c1a5_subset_map Y (Set.inter_subset_right : U' ∩ V' ⊆ V'))
  let q' := TopCat.toSSet.map (topologicalSubsetInclusion Y U')
  let a' := TopCat.toSSet.map (c1a5_subset_map Y (Set.inter_subset_left : U' ∩ V' ⊆ U'))
  let b' := TopCat.toSSet.map (topologicalSubsetInclusion Y V')
  let u := TopCat.toSSet.map (c1a5_map_subspace f (U ∩ V) (U' ∩ V')
    (fun x hx ↦ ⟨hfU x hx.1, hfV x hx.2⟩))
  let v := TopCat.toSSet.map (c1a5_map_subspace f V V' hfV)
  let s := TopCat.toSSet.map (c1a5_map_subspace f U U' hfU)
  let t := TopCat.toSSet.map f
  have w : p ≫ b = a ≫ q := by
    dsimp [p, b, a, q]
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl
  have w' : p' ≫ b' = a' ≫ q' := by
    dsimp [p', b', a', q']
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl
  have wp : p ≫ v = u ≫ p' := by
    dsimp [p, v, u, p']
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl
  have wq : q ≫ t = s ≫ q' := by
    dsimp [q, t, s, q']
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl
  have wa : a ≫ s = u ≫ a' := by
    dsimp [a, s, u, a']
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl
  have wb : b ≫ t = v ≫ b' := by
    dsimp [b, t, v, b']
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl
  have hm : Mono (c1a5_subset_map X (Set.inter_subset_right : U ∩ V ⊆ V)) :=
    (TopCat.mono_iff_injective _).2 (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : TopCat.of V ↦ (z.val : X)) h))
  have hm' : Mono (c1a5_subset_map Y (Set.inter_subset_right : U' ∩ V' ⊆ V')) :=
    (TopCat.mono_iff_injective _).2 (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : TopCat.of V' ↦ (z.val : Y)) h))
  have hc : QuasiIso (c1a5RelativeMap c1a5Chains p p' u v wp) := by
    have := c1a5_chains_map_mono p
    have := c1a5_chains_map_mono p'
    exact c1a5_cokernel_comparison (c1a5Chains.map p) (c1a5Chains.map p')
      (c1a5Chains.map u) (c1a5Chains.map v)
      (by rw [← c1a5Chains.map_comp, ← c1a5Chains.map_comp, wp]) hi hv
  exact c1a5_relative_cube_comparison c1a5Chains p q a b p' q' a' b' u v s t
    w w' wp wq wa wb
    (c1a5_subspace_open_cover_excision X U V hU hV hX)
    (c1a5_subspace_open_cover_excision Y U' V' hU' hV' hY) hc

end HodgeLean.Foundations.Program
