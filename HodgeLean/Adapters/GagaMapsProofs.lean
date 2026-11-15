import HodgeLean.Adapters.GagaMapsDefs
import HodgeLean.Adapters.AbelianEndomorphisms2
import HodgeLean.Foundations.SegreProjective
import HodgeLean.Foundations.Mathlib.ZmtIso

/-! # Proof obligations for algebraizing holomorphic maps -/

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped Manifold ContDiff MonoidalCategory
open HodgeLean.Foundations

namespace HodgeLean.Adapters

/-- Products of integral complex schemes are integral.
Source: Stacks Project, Tag 05P3; `isIntegral_pullback_of_isAlgClosed`. -/
instance gagam_product_isIntegral (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    IsIntegral (gagam_product X Y).left := by
  change IsIntegral (Limits.pullback X.hom Y.hom)
  exact HodgeLean.Foundations.isIntegral_pullback_of_isAlgClosed ℂ X.left Y.left X.hom Y.hom

/-- Products of smooth complex schemes are smooth.
Source: Mathlib, stability of smooth morphisms under base change and composition. -/
instance gagam_product_smooth (X Y : Over (Spec ↧ℂ)) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (gagam_product X Y).hom := by
  dsimp [gagam_product]
  infer_instance

/-- Products of projective complex schemes are projective.
Source: EGA II, 5.5.5; Mathlib, stability of projective morphisms under products. -/
instance gagam_product_projective (X Y : Over (Spec ↧ℂ))
    [IsProjective X.hom] [IsProjective Y.hom] : IsProjective (gagam_product X Y).hom := by
  exact HodgeLean.Foundations.spec_g3c_isProjective_pullback X.hom Y.hom

/-- An `ω`-smooth map between complex manifolds is analytic in any pair of preferred charts
whose sources contain the point and its image. -/
private theorem gagam_analyticAt_chart {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] {M M' : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace M'] [ChartedSpace E' M']
    [IsManifold (modelWithCornersSelf ℂ E) ω M] [IsManifold (modelWithCornersSelf ℂ E') ω M']
    {G : M → M'} (hG : ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E') ω G)
    (p : M) (y : M') {z : E} (hz : z ∈ (chartAt E p).target)
    (hy : G ((chartAt E p).symm z) ∈ (chartAt E' y).source) :
    AnalyticAt ℂ (fun v => chartAt E' y (G ((chartAt E p).symm v))) z := by
  have hq : (chartAt E p).symm z ∈ (chartAt E p).source := (chartAt E p).map_target hz
  have h := ((contMDiffAt_iff_of_mem_source hq hy).1 (hG _)).2
  have h' : ContDiffWithinAt ℂ ω (chartAt E' y ∘ G ∘ (chartAt E p).symm) Set.univ z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, (chartAt E p).right_inv hz] using h
  exact (h'.contDiffAt Filter.univ_mem).analyticAt

theorem gagam_graph_closedAnalytic_aux (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    IsClosedAnalytic (Fin (dim (gagam_product X Y).left) → ℂ) (gagam_graph X Y F) := by
  classical
  set P := gagam_product X Y
  set G₁ : ComplexPoint P → ComplexPoint Y :=
    Point.map (CartesianMonoidalCategory.snd X Y) with hG₁
  set G₂ : ComplexPoint P → ComplexPoint Y :=
    F ∘ Point.map (CartesianMonoidalCategory.fst X Y) with hG₂
  have hG₁s : ContMDiff (modelWithCornersSelf ℂ (Fin (dim P.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω G₁ :=
    spec_contMDiff_pointMap P Y (dim P.left) (dim Y.left) _
  have hG₂s : ContMDiff (modelWithCornersSelf ℂ (Fin (dim P.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω G₂ :=
    hF.comp (spec_contMDiff_pointMap P X (dim P.left) (dim X.left) _)
  have hgraph : gagam_graph X Y F = {z | G₁ z = G₂ z} := rfl
  refine ⟨hgraph ▸ isClosed_eq hG₁s.continuous hG₂s.continuous, ?_⟩
  intro p hp
  set φ := chartAt (Fin (dim P.left) → ℂ) p
  set ψ := chartAt (Fin (dim Y.left) → ℂ) (G₁ p)
  set U := φ.target ∩ φ.symm ⁻¹' (G₁ ⁻¹' ψ.source ∩ G₂ ⁻¹' ψ.source)
  have hpφ : p ∈ φ.source := mem_chart_source _ p
  refine ⟨U, φ.isOpen_inter_preimage_symm
    ((ψ.open_source.preimage hG₁s.continuous).inter (ψ.open_source.preimage hG₂s.continuous)),
    ⟨φ.map_source hpφ, ?_, ?_⟩, Set.inter_subset_left, dim Y.left,
    fun i v => ψ (G₁ (φ.symm v)) i - ψ (G₂ (φ.symm v)) i, ?_, ?_⟩
  · simp only [Set.mem_preimage, φ.left_inv hpφ]
    exact mem_chart_source _ _
  · simp only [Set.mem_preimage, φ.left_inv hpφ]
    rw [show G₂ p = G₁ p from hp.symm]
    exact mem_chart_source _ _
  · intro i v hv
    have h₁ := gagam_analyticAt_chart hG₁s p (G₁ p) hv.1 hv.2.1
    have h₂ := gagam_analyticAt_chart hG₂s p (G₁ p) hv.1 hv.2.2
    have hπ := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (dim Y.left) => ℂ) i).analyticAt
    exact ((hπ _).comp h₁).sub ((hπ _).comp h₂)
  · intro v hv
    change G₁ (φ.symm v) = G₂ (φ.symm v) ↔ _
    simp only [sub_eq_zero]
    rw [← funext_iff]
    exact ⟨fun h => by rw [h], fun h => ψ.injOn hv.2.1 hv.2.2 h⟩

theorem gagam_graph_closed_aux (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    ∃ C : Set (gagam_product X Y).left, IsClosed C ∧
      gagam_graph X Y F =
        (Point.underlying : ComplexPoint (gagam_product X Y) →
          (gagam_product X Y).left) ⁻¹' C := by
  exact chowG_setLevel (gagam_product X Y) _ (gagam_graph_closedAnalytic_aux X Y F hF)

/-- The reduced induced closed-subscheme structure on a closed set is reduced: its affine charts
are quotients by vanishing ideals, which are radical. -/
private theorem gagam_isReduced_subscheme {Z : Scheme.{0}} (S : Closeds Z) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal S
  have h : ∀ U : Z.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    have : _root_.IsReduced (Γ(Z, U.1) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).1 (PrimeSpectrum.isRadical_vanishingIdeal _)
    change IsReduced (Spec (CommRingCat.of (Γ(Z, U.1) ⧸ I.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover _ I.subschemeCover.openCover h

/-- The underlying point of a complex point of a complex scheme locally of finite type is
closed. -/
private theorem gagam_isClosed_underlying {W : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom]
    (z : ComplexPoint W) : IsClosed ({z.underlying} : Set W.left) :=
  ((pointEquivClosedPoint W.hom) ⟨z.left, by simp⟩).2

/-- Every closed point of a complex scheme locally of finite type underlies a complex point. -/
private theorem gagam_exists_underlying {W : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom]
    (x : W.left) (hx : IsClosed ({x} : Set W.left)) :
    ∃ z : ComplexPoint W, z.underlying = x :=
  ⟨Over.homMk (pointOfClosedPoint W.hom x hx) (by simp), pointOfClosedPoint_apply W.hom x hx _⟩

/-- The residue field map at a closed point of a morphism between complex schemes locally of
finite type is an isomorphism. -/
private theorem gagam_isIso_residueFieldMap {A B : Scheme.{0}} (sA : A ⟶ Spec ↧ℂ)
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

theorem gagam_morphism_of_closed_graph_aux (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (C : Set (gagam_product X Y).left) (hC : IsClosed C)
    (hgraph : gagam_graph X Y F =
      (Point.underlying : ComplexPoint (gagam_product X Y) →
        (gagam_product X Y).left) ⁻¹' C) :
    ∃ f : X ⟶ Y, Point.map f = F := by
  classical
  have : LocallyOfFiniteType (gagam_product X Y).hom := by
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
  have hmem : ∀ w : ComplexPoint (gagam_product X Y),
      w ∈ gagam_graph X Y F ↔ w.underlying ∈ C := fun w => by
    rw [hgraph]; rfl
  have hfst : ∀ w : ComplexPoint (gagam_product X Y),
      (Point.map (CartesianMonoidalCategory.fst X Y) w).underlying =
        Limits.pullback.fst X.hom Y.hom w.underlying := fun w => rfl
  -- closed points of `Γ` come from graph points
  have hclosedP : ∀ z : Γ, IsClosed ({z} : Set Γ) →
      IsClosed ({ι z} : Set (Limits.pullback X.hom Y.hom : Scheme)) := fun z hz => by
    simpa using ι.isClosedEmbedding.isClosedMap _ hz
  have hgraphpt : ∀ z : Γ, IsClosed ({z} : Set Γ) →
      ∃ w : ComplexPoint (gagam_product X Y), w.underlying = ι z ∧ w ∈ gagam_graph X Y F :=
        fun z hz => by
    obtain ⟨w, hw⟩ := gagam_exists_underlying (W := gagam_product X Y) (ι z) (hclosedP z hz)
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
    obtain ⟨a, ha⟩ := gagam_exists_underlying (W := X) x hx
    let w : ComplexPoint (gagam_product X Y) := CartesianMonoidalCategory.lift a (F a)
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
        rw [hz]; exact gagam_isClosed_underlying w
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
  have : IsReduced Γ := gagam_isReduced_subscheme _
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
    gagam_isIso_residueFieldMap (pr ≫ X.hom) X.hom pr rfl z hz (hprc z hz)
  have : IsIso pr := zmtiso_isIso_of_proper_injective_normal (k := ℂ) (pr ≫ X.hom) X.hom pr
    (zmtiso_normal_of_smooth X.left X.hom) rfl hinj hsurj hres
  have hw : (inv pr ≫ ι ≫ Limits.pullback.snd X.hom Y.hom) ≫ Y.hom = X.hom := by
    have hc : ι ≫ Limits.pullback.snd X.hom Y.hom ≫ Y.hom = pr ≫ X.hom := by
      rw [hpr, Category.assoc, Limits.pullback.condition]
    simp only [Category.assoc]
    rw [hc, IsIso.inv_hom_id_assoc]
  refine ⟨Over.homMk (inv pr ≫ ι ≫ Limits.pullback.snd X.hom Y.hom) hw, funext fun a => ?_⟩
  let w : ComplexPoint (gagam_product X Y) := Over.homMk (a.left ≫ inv pr ≫ ι) (by
    change (a.left ≫ inv pr ≫ ι) ≫ Limits.pullback.fst X.hom Y.hom ≫ X.hom = _
    simp only [Category.assoc]
    rw [← Category.assoc ι, ← hpr, IsIso.inv_hom_id_assoc]
    exact Over.w a)
  have hwfst : Point.map (CartesianMonoidalCategory.fst X Y) w = a := by
    apply Over.OverMorphism.ext
    change (a.left ≫ inv pr ≫ ι) ≫ Limits.pullback.fst X.hom Y.hom = a.left
    simp only [Category.assoc]
    rw [← hpr, IsIso.inv_hom_id, Category.comp_id]
  have hwC : w.underlying ∈ C := by
    rw [← hrange]
    exact ⟨(a.left ≫ inv pr) (IsLocalRing.closedPoint ℂ), rfl⟩
  have hg : Point.map (CartesianMonoidalCategory.snd X Y) w =
      F (Point.map (CartesianMonoidalCategory.fst X Y) w) := (hmem w).2 hwC
  rw [hwfst] at hg
  rw [← hg]
  apply Over.OverMorphism.ext
  change a.left ≫ inv pr ≫ ι ≫ Limits.pullback.snd X.hom Y.hom =
    (a.left ≫ inv pr ≫ ι) ≫ Limits.pullback.snd X.hom Y.hom
  simp only [Category.assoc]

theorem gagam_algebraize_aux (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    ∃ f : X ⟶ Y, Point.map f = F := by
  obtain ⟨C, hC, hgraph⟩ := gagam_graph_closed_aux X Y F hF
  exact gagam_morphism_of_closed_graph_aux X Y F C hC hgraph

theorem gagam_hAlg_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
        (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ)) ω F →
        ∃ h : X ⟶ X, Point.map h = F := by
  intro F hF
  exact gagam_algebraize_aux X X F hF

end HodgeLean.Adapters
