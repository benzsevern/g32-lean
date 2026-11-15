import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-! Monomorphism transport through the relative skeletal presentation.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- A colimit functor into types preserves attachment inclusions when each attaching boundary
map has monomorphic image.
Source: Mathlib AttachCells.isPushout and stability of type monomorphisms under pushouts. -/
lemma c1a5_map_attach_mono (G : SSet.{0} ⥤ Type) [PreservesColimits G]
    {J : Type} {A B : J → SSet.{0}} (g : ∀ j, A j ⟶ B j)
    {X Y : SSet.{0}} {f : X ⟶ Y} (c : HomotopicalAlgebra.AttachCells.{0} g f)
    (hg : ∀ j, Mono (G.map (g j))) : Mono (G.map f) := by
  let C₁ := Cofan.mk (G.obj c.cofan₁.pt) (fun i ↦ G.map (c.cofan₁.inj i))
  let C₂ := Cofan.mk (G.obj c.cofan₂.pt) (fun i ↦ G.map (c.cofan₂.inj i))
  have hc₁ : IsColimit C₁ := isColimitCofanMkObjOfIsColimit G _ _ c.isColimit₁
  have hc₂ : IsColimit C₂ := isColimitCofanMkObjOfIsColimit G _ _ c.isColimit₂
  have hm : Mono (G.map c.m) := by
    rw [mono_iff_injective]
    intro x y h
    obtain ⟨i, x, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hc₁ x
    obtain ⟨j, y, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hc₁ y
    have hw (k : c.ι) : G.map (c.cofan₁.inj k) ≫ G.map c.m =
        G.map (g (c.π k)) ≫ G.map (c.cofan₂.inj k) := by
      rw [← G.map_comp, c.hm, G.map_comp]
    have h' : C₂.inj i (G.map (g (c.π i)) x) = C₂.inj j (G.map (g (c.π j)) y) := by
      change G.map c.m (G.map (c.cofan₁.inj i) x) =
        G.map c.m (G.map (c.cofan₁.inj j) y) at h
      exact ((ConcreteCategory.congr_hom (hw i) x).symm.trans h).trans
        (ConcreteCategory.congr_hom (hw j) y)
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit hc₂ _ _ h'
    have hxy := Cofan.inj_injective_of_isColimit hc₂ i h'
    have := hg (c.π i)
    obtain rfl := (mono_iff_injective (G.map (g (c.π i)))).1 inferInstance hxy
    rfl
  exact (monomorphisms (Type)).of_isPushout (c.isPushout.map G) hm

/-- A type-valued colimit functor takes simplicial monomorphisms to monomorphisms
once it does so for the actual boundary generators.
Source: Mathlib SSet.relativeCellComplexOfMono and Types.Monomorphisms. -/
lemma c1a5_map_mono_of_boundary_mono (G : SSet.{0} ⥤ Type) [PreservesColimits G]
    (hboundary : ∀ n, Mono (G.map (SSet.boundary.{0} n).ι))
    {A B : SSet.{0}} (f : A ⟶ B) [Mono f] : Mono (G.map f) := by
  have : PreservesWellOrderContinuousOfShape ℕ G := {}
  let c := SSet.relativeCellComplexOfMono f
  let h : (monomorphisms (Type)).TransfiniteCompositionOfShape ℕ (G.map f) :=
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map G
      map_mem j hj := by
        change Mono (G.map (c.F.map (homOfLE (Order.le_succ j))))
        exact c1a5_map_attach_mono G _ (c.attachCells j hj) (fun _ ↦ hboundary j) }
  exact (monomorphisms (Type)).transfiniteCompositionsOfShape_le ℕ _ h.mem

/-- Every point of a realized boundary is represented by a codimension one face.
Source: Mathlib SSet.boundary.hom_ext, sigmaComparison and sSetTopAdj. -/
lemma c1a5_boundary_realization_exists_face (n : ℕ)
    (x : SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet)) :
    ∃ (i : Fin (n + 2)) (y : SSet.toTop.obj (Δ[n] : SSet.{0})),
      SSet.toTop.map (SSet.boundary.ι i) y = x := by
  let K : Fin (n + 2) → SSet.{0} := fun _ ↦ Δ[n]
  let f : (∐ K) ⟶ (SSet.boundary.{0} (n + 1) : SSet) :=
    CategoryTheory.Limits.Sigma.desc (fun i ↦ SSet.boundary.ι i)
  have : Epi f := by
    constructor
    intro Z a b hab
    apply SSet.boundary.hom_ext
    intro i
    have h := CategoryTheory.Limits.Sigma.ι K i ≫= hab
    simpa only [f, CategoryTheory.Limits.Sigma.ι_comp_desc_assoc] using h
  let G := SSet.toTop.{0} ⋙ forget TopCat
  have hf : Function.Surjective (G.map f) := (epi_iff_surjective _).1 inferInstance
  obtain ⟨z, hz⟩ := hf x
  let C := Cofan.mk (G.obj (∐ K)) (fun i ↦ G.map (CategoryTheory.Limits.Sigma.ι K i))
  have hc : IsColimit C := isColimitCofanMkObjOfIsColimit G K _ (coproductIsCoproduct K)
  obtain ⟨i, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hc z
  refine ⟨i, y, ?_⟩
  have hw : G.map (CategoryTheory.Limits.Sigma.ι K i) ≫ G.map f =
      G.map (SSet.boundary.ι i) := by
    rw [← G.map_comp]
    congr 1
    exact CategoryTheory.Limits.Sigma.ι_comp_desc _ _
  exact (ConcreteCategory.congr_hom hw y).symm.trans ((congrArg (G.map f) hy).trans hz)

end HodgeLean.Foundations.Program
