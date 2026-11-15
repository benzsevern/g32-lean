import HodgeLean.Adapters.GagaMaps
import HodgeLean.Foundations.Program.TorusAlgebraizationDefs

/-! # Graph projections of maps with a Zariski closed graph

For integral smooth projective complex schemes `X`, `Y` and a map `F` of complex points whose
graph is the set of complex points of a Zariski closed set, the first projection of the reduced
graph `b5_graph X Y F` is an isomorphism, and the induced morphism `X ⟶ Y` realizes `F`.
The argument is the one of `gagam_morphism_of_closed_graph_aux`.
-/

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped MonoidalCategory
open HodgeLean.Foundations HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The reduced induced closed-subscheme structure on a closed set is reduced. -/
theorem b55_isReduced_subscheme {Z : Scheme.{0}} (S : Closeds Z) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal S
  have h : ∀ U : Z.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    have : _root_.IsReduced (Γ(Z, U.1) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).1 (PrimeSpectrum.isRadical_vanishingIdeal _)
    change IsReduced (Spec (CommRingCat.of (Γ(Z, U.1) ⧸ I.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover _ I.subschemeCover.openCover h

private theorem b55_isClosed_underlying {W : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom]
    (z : ComplexPoint W) : IsClosed ({z.underlying} : Set W.left) :=
  ((pointEquivClosedPoint W.hom) ⟨z.left, by simp⟩).2

private theorem b55_exists_underlying {W : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom]
    (x : W.left) (hx : IsClosed ({x} : Set W.left)) :
    ∃ z : ComplexPoint W, z.underlying = x :=
  ⟨Over.homMk (pointOfClosedPoint W.hom x hx) (by simp), pointOfClosedPoint_apply W.hom x hx _⟩

private theorem b55_isIso_residueFieldMap {A B : Scheme.{0}} (sA : A ⟶ Spec ↧ℂ)
    (sB : B ⟶ Spec ↧ℂ) [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] (g : A ⟶ B)
    (hg : g ≫ sB = sA) (a : A) (ha : IsClosed ({a} : Set A)) (hga : IsClosed ({g a} : Set B)) :
    IsIso (g.residueFieldMap a) := by
  have h : (residueFieldIsoBase sB (g a) hga).inv ≫ g.residueFieldMap a =
      (residueFieldIsoBase sA a ha).inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv,
      SpecMap_residueFieldIsoBase_inv,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
      hg]
  have : g.residueFieldMap a = (residueFieldIsoBase sB (g a) hga).hom ≫
      (residueFieldIsoBase sA a ha).inv := by
    rw [← h, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance

/-- The reduced subscheme on a Zariski closed carrier of a graph projects isomorphically onto
the source.
Source: Hartshorne, *Algebraic Geometry*, Chapter III, Corollary 11.4; EGA III, 4.4. -/
theorem b55_isIso_subscheme_fst (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (C : Set (X ⊗ Y).left) (hC : IsClosed C)
    (hgraph : gagam_graph X Y F =
      (Point.underlying : ComplexPoint (X ⊗ Y) → (X ⊗ Y).left) ⁻¹' C) :
    IsIso ((Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hC⟩ : Closeds (X ⊗ Y).left)).subschemeι ≫ Limits.pullback.fst X.hom Y.hom) := by
  classical
  have : LocallyOfFiniteType (X ⊗ Y).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst X.hom Y.hom ≫ X.hom)
    infer_instance
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨C, hC⟩ : Closeds (Limits.pullback X.hom Y.hom : Scheme)) with hI
  set Γ := I.subscheme
  set ι : Γ ⟶ Limits.pullback X.hom Y.hom := I.subschemeι with hι
  have hrange : Set.range ι = C := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hιinj : Function.Injective ι := ι.isClosedEmbedding.injective
  have : IsClosedImmersion ι := by rw [hι]; infer_instance
  set pr : Γ ⟶ X.left := ι ≫ Limits.pullback.fst X.hom Y.hom with hpr
  have hmem : ∀ w : ComplexPoint (X ⊗ Y),
      w ∈ gagam_graph X Y F ↔ w.underlying ∈ C := fun w => by
    rw [hgraph]; rfl
  have hfst : ∀ w : ComplexPoint (X ⊗ Y),
      (Point.map (CartesianMonoidalCategory.fst X Y) w).underlying =
        Limits.pullback.fst X.hom Y.hom w.underlying := fun w => rfl
  have hclosedP : ∀ z : Γ, IsClosed ({z} : Set Γ) →
      IsClosed ({ι z} : Set (Limits.pullback X.hom Y.hom : Scheme)) := fun z hz => by
    simpa using ι.isClosedEmbedding.isClosedMap _ hz
  have hgraphpt : ∀ z : Γ, IsClosed ({z} : Set Γ) →
      ∃ w : ComplexPoint (X ⊗ Y), w.underlying = ι z ∧ w ∈ gagam_graph X Y F :=
        fun z hz => by
    obtain ⟨w, hw⟩ := b55_exists_underlying (W := X ⊗ Y) (ι z) (hclosedP z hz)
    refine ⟨w, hw, (hmem w).2 ?_⟩
    rw [hw, ← hrange]; exact ⟨z, rfl⟩
  have hinj : ∀ ⦃z₁ z₂ : Γ⦄, IsClosed ({z₁} : Set Γ) → IsClosed ({z₂} : Set Γ) →
      pr z₁ = pr z₂ → z₁ = z₂ := by
    intro z₁ z₂ h₁ h₂ h
    obtain ⟨w₁, hw₁, hg₁⟩ := hgraphpt z₁ h₁
    obtain ⟨w₂, hw₂, hg₂⟩ := hgraphpt z₂ h₂
    have e₁ : Point.map (CartesianMonoidalCategory.fst X Y) w₁ =
        Point.map (CartesianMonoidalCategory.fst X Y) w₂ := by
      apply underlying_injective_of_locallyOfFiniteType
      rw [hfst, hfst, hw₁, hw₂]
      exact h
    have e₂ : Point.map (CartesianMonoidalCategory.snd X Y) w₁ =
        Point.map (CartesianMonoidalCategory.snd X Y) w₂ := by
      rw [show _ = _ from hg₁, show _ = _ from hg₂, e₁]
    have : w₁ = w₂ := CartesianMonoidalCategory.hom_ext _ _ e₁ e₂
    apply hιinj
    rw [← hw₁, ← hw₂, this]
  have hsurj : ∀ x : X.left, IsClosed ({x} : Set X.left) →
      ∃ z : Γ, IsClosed ({z} : Set Γ) ∧ pr z = x := by
    intro x hx
    obtain ⟨a, ha⟩ := b55_exists_underlying (W := X) x hx
    let w : ComplexPoint (X ⊗ Y) := CartesianMonoidalCategory.lift a (F a)
    have hwfst : Point.map (CartesianMonoidalCategory.fst X Y) w = a :=
      CartesianMonoidalCategory.lift_fst _ _
    have hwsnd : Point.map (CartesianMonoidalCategory.snd X Y) w = F a :=
      CartesianMonoidalCategory.lift_snd _ _
    have hwC : w.underlying ∈ C := (hmem w).1 (by
      change Point.map (CartesianMonoidalCategory.snd X Y) w =
        F (Point.map (CartesianMonoidalCategory.fst X Y) w)
      rw [hwfst, hwsnd])
    rw [← hrange] at hwC
    obtain ⟨z, hz⟩ := hwC
    refine ⟨z, ?_, ?_⟩
    · have h1 : IsClosed ({ι z} : Set (Limits.pullback X.hom Y.hom : Scheme)) := by
        rw [hz]; exact b55_isClosed_underlying w
      have h2 : ({z} : Set Γ) = ι ⁻¹' {ι z} := by ext; simp [hιinj.eq_iff]
      rw [h2]
      exact h1.preimage ι.continuous
    · change Limits.pullback.fst X.hom Y.hom (ι z) = x
      rw [hz, ← hfst, hwfst, ha]
  have : LocallyOfFiniteType (pr ≫ X.hom) := by rw [hpr]; infer_instance
  have : JacobsonSpace Γ := LocallyOfFiniteType.jacobsonSpace (pr ≫ X.hom)
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : IsProper pr := by rw [hpr]; infer_instance
  have hprc : ∀ z : Γ, IsClosed ({z} : Set Γ) → IsClosed ({pr z} : Set X.left) := fun z hz => by
    simpa using pr.isClosedMap _ hz
  have : IsReduced Γ := b55_isReduced_subscheme _
  have key : ∀ A : Set Γ, IsClosed A → Set.univ ⊆ pr '' A → Set.univ ⊆ A := by
    intro A hA hAu
    have hcl : closedPoints Γ ⊆ A := by
      intro z hz
      obtain ⟨a, haA, ha⟩ := hAu (Set.mem_univ (pr z))
      obtain ⟨a', ⟨ha'A, ha'f⟩, ha'c⟩ := nonempty_inter_closedPoints
        (Z := A ∩ pr ⁻¹' {pr z}) ⟨a, haA, ha⟩
        (hA.inter ((hprc z hz).preimage pr.continuous)).isLocallyClosed
      rwa [hinj ha'c hz ha'f] at ha'A
    rw [← closure_closedPoints]
    exact closure_minimal hcl hA
  have : IrreducibleSpace Γ := by
    rw [irreducibleSpace_def]
    obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (X := X.left) Set.univ_nonempty
      isClosed_univ.isLocallyClosed
    obtain ⟨z, -, -⟩ := hsurj x hx
    refine ⟨⟨z, Set.mem_univ _⟩, ?_⟩
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro A B hA hB hAB
    have hcov : (Set.univ : Set X.left) ⊆ pr '' A ∪ pr '' B := by
      rw [← closure_closedPoints]
      refine closure_minimal (fun x hx => ?_) ((pr.isClosedMap _ hA).union (pr.isClosedMap _ hB))
      obtain ⟨z, -, rfl⟩ := hsurj x hx
      rcases hAB (Set.mem_univ z) with h | h
      · exact Or.inl ⟨z, h, rfl⟩
      · exact Or.inr ⟨z, h, rfl⟩
    rcases (isPreirreducible_iff_isClosed_union_isClosed.1
      (IrreducibleSpace.isIrreducible_univ X.left).2) _ _ (pr.isClosedMap _ hA)
      (pr.isClosedMap _ hB) hcov with h | h
    · exact Or.inl (key A hA h)
    · exact Or.inr (key B hB h)
  have : IsIntegral Γ := isIntegral_of_irreducibleSpace_of_isReduced Γ
  have hres : ∀ z : Γ, IsClosed ({z} : Set Γ) → IsIso (pr.residueFieldMap z) := fun z hz =>
    b55_isIso_residueFieldMap (pr ≫ X.hom) X.hom pr rfl z hz (hprc z hz)
  exact zmtiso_isIso_of_proper_injective_normal (k := ℂ) (pr ≫ X.hom) X.hom pr
    (zmtiso_normal_of_smooth X.left X.hom) rfl hinj hsurj hres

/-- A Zariski closed carrier can be replaced by the closure of the graph's underlying points. -/
theorem b55_graph_eq_preimage_closure (X Y : Over (Spec ↧ℂ))
    (F : ComplexPoint X → ComplexPoint Y)
    (C : Set (X ⊗ Y).left) (hC : IsClosed C)
    (hgraph : gagam_graph X Y F =
      (Point.underlying : ComplexPoint (X ⊗ Y) → (X ⊗ Y).left) ⁻¹' C) :
    gagam_graph X Y F = (Point.underlying : ComplexPoint (X ⊗ Y) → (X ⊗ Y).left) ⁻¹'
      closure (Point.underlying '' gagam_graph X Y F) := by
  apply Set.Subset.antisymm
  · intro w hw
    exact subset_closure ⟨w, hw, rfl⟩
  · intro w hw
    have hsub : closure (Point.underlying '' gagam_graph X Y F) ⊆ C := by
      refine closure_minimal ?_ hC
      rintro _ ⟨v, hv, rfl⟩
      rw [hgraph] at hv
      exact hv
    rw [hgraph]
    exact hsub hw

/-- The first projection of the reduced graph is an isomorphism when the graph has a Zariski
closed carrier.
Source: Serre, GAGA, §3, Proposition 13; Hartshorne, Chapter III, Corollary 11.4. -/
theorem b55_graphFirst_isIso (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (C : Set (X ⊗ Y).left) (hC : IsClosed C)
    (hgraph : gagam_graph X Y F =
      (Point.underlying : ComplexPoint (X ⊗ Y) → (X ⊗ Y).left) ⁻¹' C) :
    IsIso (b5_graphFirst X Y F) := by
  have h := b55_isIso_subscheme_fst X Y F _ isClosed_closure
    (b55_graph_eq_preimage_closure X Y F C hC hgraph)
  have : IsIso ((Over.forget _).map (b5_graphFirst X Y F)) := h
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The morphism read off from the graph realizes the given map on complex points.
Source: Serre, GAGA, §3, Proposition 13. -/
theorem b55_pointMap_graph (X Y : Over (Spec ↧ℂ))
    (F : ComplexPoint X → ComplexPoint Y)
    (C : Set (X ⊗ Y).left) (hC : IsClosed C)
    (hgraph : gagam_graph X Y F =
      (Point.underlying : ComplexPoint (X ⊗ Y) → (X ⊗ Y).left) ⁻¹' C)
    [IsIso (b5_graphFirst X Y F)] :
    Point.map (inv (b5_graphFirst X Y F) ≫ b5_graphSecond X Y F) = F := by
  funext a
  have hD := b55_graph_eq_preimage_closure X Y F C hC hgraph
  let w : ComplexPoint (X ⊗ Y) := a ≫ inv (b5_graphFirst X Y F) ≫ b5_graphInclusion X Y F
  have hwfst : Point.map (CartesianMonoidalCategory.fst X Y) w = a := by
    change (a ≫ inv (b5_graphFirst X Y F) ≫ b5_graphInclusion X Y F) ≫
      CartesianMonoidalCategory.fst X Y = a
    simp only [Category.assoc]
    change a ≫ inv (b5_graphFirst X Y F) ≫ b5_graphFirst X Y F = a
    simp
  have hwmem : w ∈ gagam_graph X Y F := by
    rw [hD]
    have hr : w.underlying ∈ Set.range (b5_graphIdeal X Y F).subschemeι :=
      ⟨(a ≫ inv (b5_graphFirst X Y F)).left (IsLocalRing.closedPoint ℂ), rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at hr
    exact hr
  have hg : Point.map (CartesianMonoidalCategory.snd X Y) w =
      F (Point.map (CartesianMonoidalCategory.fst X Y) w) := hwmem
  rw [hwfst] at hg
  rw [← hg]
  change a ≫ inv (b5_graphFirst X Y F) ≫ b5_graphInclusion X Y F ≫
    CartesianMonoidalCategory.snd X Y = (a ≫ inv (b5_graphFirst X Y F) ≫
      b5_graphInclusion X Y F) ≫ CartesianMonoidalCategory.snd X Y
  simp only [Category.assoc]

/-- Morphisms over `Spec ℂ` out of a reduced scheme of finite type into a separated scheme of
finite type are determined by their maps of complex points.
Source: Mathlib `AlgebraicGeometry.ext_of_apply_eq`. -/
theorem b55_hom_ext {Y X : Over (Spec ↧ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    {f g : Y ⟶ X} (h : Point.map f = Point.map g) : f = g := by
  refine Over.OverMorphism.ext ?_
  have hf : f.left ≫ X.hom = Y.hom := Over.w f
  have hg : g.left ≫ X.hom = Y.hom := Over.w g
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply Y.hom x hx a]
  have := congrArg (fun z => z.left)
    (congrFun h (Over.homMk (pointOfClosedPoint Y.hom x hx) (by simp) :
      Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y))
  change (pointOfClosedPoint Y.hom x hx ≫ f.left) a = (pointOfClosedPoint Y.hom x hx ≫ g.left) a
  exact congrArg (fun φ : Spec ↧ℂ ⟶ X.left => φ a) this

end HodgeLean.Foundations.Program
