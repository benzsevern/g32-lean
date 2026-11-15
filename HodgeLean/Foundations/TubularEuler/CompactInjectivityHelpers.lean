import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Separation.Hausdorff

/-! # Compact injectivity for a supplied family of local inverses

The resulting open set retains the supplied map and lies in the local-inverse cover.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.TubularEuler

theorem compact_partial_homeomorph_shrinking {B X Y : Type*}
    [TopologicalSpace B] [CompactSpace B] [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (U : Opens X) (z : C(B, U)) (f : C(U, Y))
    (hz : Function.Injective (f ∘ z))
    (e : B → OpenPartialHomeomorph X Y)
    (he : ∀ b, (z b).val ∈ (e b).source)
    (heU : ∀ b, (e b).source ⊆ U)
    (hemap : ∀ b x hx, e b x = f ⟨x, heU b hx⟩) :
    ∃ O : Opens X, ∃ hsub : (O : Set X) ⊆ U,
      (∀ b, (z b).val ∈ O) ∧
      (∀ x ∈ O, ∃ b, x ∈ (e b).source) ∧
      Function.Injective (fun x : O => f ⟨x.val, hsub x.property⟩) := by
  have hinj : Set.InjOn f (Set.range z) := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ h
    exact congrArg z (hz h)
  have hloc : ∀ u ∈ Set.range z, ∃ t ∈ 𝓝 u, Set.InjOn f t := by
    rintro _ ⟨b, rfl⟩
    let t : Set U := Subtype.val ⁻¹' (e b).source
    have ht : IsOpen t := (e b).open_source.preimage continuous_subtype_val
    refine ⟨t, ht.mem_nhds (he b), ?_⟩
    intro u hu w hw h
    apply Subtype.ext
    apply (e b).injOn hu hw
    exact (hemap b u.val hu).trans (h.trans (hemap b w.val hw).symm)
  obtain ⟨S, hS, hzS, hSi⟩ := hinj.exists_isOpen_superset
    (isCompact_range z.continuous) (fun _ _ => f.continuous.continuousAt) hloc
  let O : Opens X := ⟨Subtype.val '' S ∩ ⋃ b, (e b).source,
    (U.isOpen.isOpenMap_subtype_val _ hS).inter
      (isOpen_iUnion (fun b => (e b).open_source))⟩
  have hsub : (O : Set X) ⊆ U := by
    rintro x ⟨⟨u, hu, rfl⟩, _⟩
    exact u.property
  refine ⟨O, hsub, ?_, ?_, ?_⟩
  · intro b
    exact ⟨⟨z b, hzS ⟨b, rfl⟩, rfl⟩, Set.mem_iUnion.mpr ⟨b, he b⟩⟩
  · intro x hx
    exact Set.mem_iUnion.mp hx.2
  · intro x y h
    obtain ⟨u, hu, hux⟩ := x.property.1
    obtain ⟨w, hw, hwy⟩ := y.property.1
    have hxu : (⟨x.val, hsub x.property⟩ : U) = u := Subtype.ext hux.symm
    have hyw : (⟨y.val, hsub y.property⟩ : U) = w := Subtype.ext hwy.symm
    have heq : f u = f w := by simpa only [hxu, hyw] using h
    apply Subtype.ext
    exact hux.symm.trans ((congrArg Subtype.val (hSi hu hw heq)).trans hwy)

theorem isOpenMap_of_partial_homeomorph_cover {B X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : Opens X) (f : C(U, Y)) (e : B → OpenPartialHomeomorph X Y)
    (heU : ∀ b, (e b).source ⊆ U)
    (hemap : ∀ b x hx, e b x = f ⟨x, heU b hx⟩)
    (hcover : ∀ u : U, ∃ b, u.val ∈ (e b).source) : IsOpenMap f := by
  intro S hS
  let A : Set X := Subtype.val '' S
  have hA : IsOpen A := U.isOpen.isOpenMap_subtype_val _ hS
  have himage : f '' S = ⋃ b, e b '' (A ∩ (e b).source) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨b, hb⟩ := hcover u
      exact Set.mem_iUnion.mpr ⟨b, u.val, ⟨⟨u, hu, rfl⟩, hb⟩, hemap b u.val hb⟩
    · intro hy
      obtain ⟨b, x, ⟨hx, hb⟩, hxy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨u, hu, (hemap b u.val hb).symm.trans hxy⟩
  rw [himage]
  exact isOpen_iUnion (fun b => (e b).isOpen_image_of_subset_source
    (hA.inter (e b).open_source) Set.inter_subset_right)

#print axioms isOpenMap_of_partial_homeomorph_cover
#print axioms compact_partial_homeomorph_shrinking

end HodgeLean.Foundations.TubularEuler
