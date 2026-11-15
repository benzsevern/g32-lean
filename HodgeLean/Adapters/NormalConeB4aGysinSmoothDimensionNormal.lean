import HodgeLean.Adapters.NormalConeB4aGysinBoundedSourceNormal
import HodgeLean.Adapters.NormalConeB4aGysinSmoothFiniteCover
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- A smooth immersed support presentation of bounded algebraic dimension has
transverse slices outside one null set, even when regional dimensions vary. -/
theorem a3b4a_gysin_smooth_dimension_normal_parameters
    (X Y : Over (Spec (CommRingCat.of ℂ))) (n c : ℕ)
    [Smooth X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsImmersion f.left] (γ : AlgebraicCycle Y.left ℚ)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) (hdim : topologicalKrullDim X.left ≤ (n : ℕ))
    (hS : ∀ y ∈ Φ.source, y ∈ a3b4_cycleSupport Y.hom γ ↔ y ∈ Set.range (Point.map f)) :
    ∃ B : Set (Fin n → ℂ), MeasureTheory.volume B = 0 ∧
      ∀ x : ComplexPoint X, Point.map f x ∈ Φ.source → (Φ (Point.map f x)).1 ∉ B →
        ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = Point.map f x ∧
          HasFDerivAt (fun v' =>
            (C.chart (Φ.symm ((Φ (Point.map f x)).1, v' + (Φ (Point.map f x)).2))).2)
            (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  classical
  have hlt : topologicalKrullDim X.left < (n + 1 : ℕ) :=
    hdim.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  obtain ⟨U, d, hU, J, hcover⟩ := a3b4a_gysin_smooth_finite_affine_dimension_cover X (n + 1) hlt
  have hf := HodgeLean.Foundations.Analytic.AnalytificationAn5_isEmbedding_map_of_immersion f
  have hregions : ∀ j : X.left, ∃ O : Set (ComplexPoint Y), IsOpen O ∧
      Point.map f ⁻¹' O = Point.overOpen (U j) := by
    intro j
    exact hf.isInducing.isOpen_iff.mp (Point.isOpen_overOpen (X := X) (U j))
  choose O hO hpre using hregions
  let Ψ : X.left → OpenPartialHomeomorph (ComplexPoint Y)
      ((Fin n → ℂ) × (Fin c → ℂ)) := fun j => Φ.restrOpen (O j) (hO j)
  have hlocal : ∀ j : X.left, ∃ B : Set (Fin n → ℂ), MeasureTheory.volume B = 0 ∧
      ∀ x : ComplexPoint X, Point.map f x ∈ (Ψ j).source →
        (Φ (Point.map f x)).1 ∉ B →
        ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = Point.map f x ∧
          HasFDerivAt (fun v' =>
            (C.chart (Φ.symm ((Φ (Point.map f x)).1, v' + (Φ (Point.map f x)).2))).2)
            (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
    intro j
    let Xj := ComplexPoint.openScheme X (U j)
    let g : Xj ⟶ Y := ComplexPoint.openInclusion X (U j) ≫ f
    letI : IsAffine Xj.left := (hU j).1
    letI : SmoothOfRelativeDimension (d j) Xj.hom := (hU j).2.2.2
    letI : LocallyOfFiniteType Xj.hom :=
      inferInstanceAs (LocallyOfFiniteType ((U j).ι ≫ X.hom))
    letI : QuasiCompact Xj.hom := inferInstance
    letI : IsSeparated Xj.hom := inferInstance
    letI : IsImmersion g.left := inferInstanceAs (IsImmersion ((U j).ι ≫ f.left))
    have hhol : a3b4_IsHolChart Y.hom (Ψ j) := by
      constructor
      · intro k
        exact HodgeLean.Foundations.Analytic.anrem_isHolFun_restrict
          (HodgeLean.Foundations.Analytic.f4_analytification Y)
          (fun _ hz => hz.1) (hΦ.1 k)
      · intro k
        exact HodgeLean.Foundations.Analytic.anrem_isHolFun_restrict
          (HodgeLean.Foundations.Analytic.f4_analytification Y)
          (fun _ hz => hz.1) (hΦ.2 k)
    have hsource : ∀ y ∈ (Ψ j).source,
        y ∈ a3b4_cycleSupport Y.hom γ ↔ y ∈ Set.range (Point.map g) := by
      intro y hy
      constructor
      · intro hys
        obtain ⟨x, rfl⟩ := (hS y hy.1).mp hys
        have hxU : x ∈ Point.overOpen (U j) := (hpre j) ▸ hy.2
        let xj := (ComplexPoint.openHomeomorph X (U j)).symm ⟨x, hxU⟩
        have hxmap : Point.map (ComplexPoint.openInclusion X (U j)) xj = x :=
          congrArg Subtype.val ((ComplexPoint.openHomeomorph X (U j)).apply_symm_apply ⟨x, hxU⟩)
        refine ⟨xj, ?_⟩
        simpa only [g, Point.map, Category.assoc] using congrArg (Point.map f) hxmap
      · rintro ⟨xj, rfl⟩
        apply (hS _ hy.1).mpr
        refine ⟨Point.map (ComplexPoint.openInclusion X (U j)) xj, ?_⟩
        simp only [g, Point.map, Category.assoc]
    obtain ⟨B, hB, hnormal⟩ := a3b4a_gysin_bounded_relative_dimension_normal_parameters
      Xj Y (d j) n c g γ (Ψ j) hhol (Nat.lt_succ_iff.mp (hU j).2.2.1) hsource
    refine ⟨B, hB, ?_⟩
    intro x hx hnot
    have hxU : x ∈ Point.overOpen (U j) := (hpre j) ▸ hx.2
    let xj := (ComplexPoint.openHomeomorph X (U j)).symm ⟨x, hxU⟩
    have hxmap : Point.map (ComplexPoint.openInclusion X (U j)) xj = x :=
      congrArg Subtype.val ((ComplexPoint.openHomeomorph X (U j)).apply_symm_apply ⟨x, hxU⟩)
    have hm : Point.map g xj = Point.map f x := by
      simpa only [g, Point.map, Category.assoc] using congrArg (Point.map f) hxmap
    have hr := hnormal xj (hm.symm ▸ hx) (hm.symm ▸ hnot)
    change ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = Point.map g xj ∧
      HasFDerivAt (fun v' =>
        (C.chart (Φ.symm ((Φ (Point.map g xj)).1, v' + (Φ (Point.map g xj)).2))).2)
        (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 at hr
    simpa only [hm] using hr
  choose B hB hnormal using hlocal
  refine ⟨⋃ j ∈ J, B j,
    (MeasureTheory.measure_biUnion_null_iff J.countable_toSet).mpr (fun j _ => hB j), ?_⟩
  intro x hx hnot
  obtain ⟨j, hj, hxU⟩ := hcover x.underlying
  have hxO : Point.map f x ∈ O j := by
    change x ∈ Point.map f ⁻¹' O j
    rw [hpre j]
    exact hxU
  apply hnormal j x ⟨hx, hxO⟩
  intro hb
  exact hnot (Set.mem_iUnion₂.mpr ⟨j, hj, hb⟩)

end HodgeLean.Adapters
