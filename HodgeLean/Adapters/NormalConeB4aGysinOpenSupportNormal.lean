import HodgeLean.Adapters.NormalConeB4aGysinBoundedSupportNormal
import HodgeLean.Adapters.NormalConeB4aGysinAlgebraicProjectionNull

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- A dimension bound on an algebraic open region gives simultaneous normal
slices of the original cycle at all chart points in that region. -/
theorem a3b4a_gysin_open_support_normal_parameters
    (Y : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (γ : AlgebraicCycle Y.left ℚ) (U : Y.left.Opens) (n c : ℕ)
    (hdim : topologicalKrullDim (reducedClosedSubscheme
      ((a3b4a_classAlgebraicSupport Y.hom γ).preimage U.ι.continuous)) ≤ (n : ℕ))
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) :
    ∃ B : Set (Fin n → ℂ), MeasureTheory.volume B = 0 ∧
      ∀ y : ComplexPoint Y, y ∈ Φ.source → y.underlying ∈ U →
        y ∈ a3b4_cycleSupport Y.hom γ → (Φ y).1 ∉ B →
        ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = y ∧
          HasFDerivAt (fun v' =>
            (C.chart (Φ.symm ((Φ y).1, v' + (Φ y).2))).2)
            (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  let Z := ComplexPoint.openScheme Y U
  let j : Z ⟶ Y := ComplexPoint.openInclusion Y U
  letI : NoetherianSpace Z.left := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : LocallyOfFiniteType Z.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Y.hom))
  letI : QuasiCompact Z.hom := inferInstance
  letI : IsSeparated Z.hom := inferInstanceAs (IsSeparated (U.ι ≫ Y.hom))
  letI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  letI : IsNoetherian Z.left := {}
  let S : Closeds Z.left := (a3b4a_classAlgebraicSupport Y.hom γ).preimage U.ι.continuous
  let R := reducedClosedSingularRemainder Z.hom S
  let W : Set (ComplexPoint Z) := {z | z.underlying ∉ R}
  have hW : IsOpen W :=
    (R.isClosed.preimage (ComplexPoint.continuous_underlying_to_zariski Z)).isOpen_compl
  have hj := ComplexPoint.isOpenEmbedding_map_open Y U
  let O := Point.map j '' W
  have hO : IsOpen O := hj.isOpenMap W hW
  let Ψ := Φ.restrOpen O hO
  let A := Over.mk (reducedClosedSmoothPieceι Z.hom S ≫ Z.hom)
  let g : A ⟶ Z := Over.homMk (reducedClosedSmoothPieceι Z.hom S) rfl
  let f : A ⟶ Y := g ≫ j
  letI : NoetherianSpace (reducedClosedSubscheme S) :=
    (reducedClosedSubschemeι S).isClosedEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace A.left :=
    (reducedClosedStructureMap Z.hom S).smoothLocus.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : Smooth A.hom :=
    inferInstanceAs (Smooth (reducedClosedSmoothPieceι Z.hom S ≫ Z.hom))
  letI : LocallyOfFiniteType A.hom :=
    inferInstanceAs (LocallyOfFiniteType (reducedClosedSmoothPieceι Z.hom S ≫ Z.hom))
  letI : QuasiCompact A.hom := inferInstance
  letI : IsSeparated A.hom :=
    inferInstanceAs (IsSeparated (reducedClosedSmoothPieceι Z.hom S ≫ Z.hom))
  letI : IsImmersion g.left :=
    inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι Z.hom S))
  letI : IsImmersion f.left :=
    inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι Z.hom S ≫ U.ι))
  have hAdim : topologicalKrullDim A.left ≤ (n : ℕ) :=
    (reducedClosedStructureMap Z.hom S).smoothLocus.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hhol : a3b4_IsHolChart Y.hom Ψ := by
    constructor
    · intro k
      exact anrem_isHolFun_restrict (f4_analytification Y) (fun _ hz => hz.1) (hΦ.1 k)
    · intro k
      exact anrem_isHolFun_restrict (f4_analytification Y) (fun _ hz => hz.1) (hΦ.2 k)
  have hsupport : ∀ z : ComplexPoint Z,
      Point.map j z ∈ a3b4_cycleSupport Y.hom γ ↔ z.underlying ∈ S := by
    intro z
    change (Point.map j z).underlying ∈ a3b4a_classAlgebraicSupport Y.hom γ ↔
      U.ι z.underlying ∈ a3b4a_classAlgebraicSupport Y.hom γ
    rw [Point.underlying_map]
    rfl
  have hrange : ∀ z : ComplexPoint Z,
      z ∈ Set.range (Point.map g) ↔ z.underlying ∈ S ∧ z.underlying ∉ R := by
    intro z
    rw [ComplexPoint.range_map_of_isImmersion_of_comm Z A g]
    change z.underlying ∈ Set.range (reducedClosedSmoothPieceι Z.hom S) ↔ _
    rw [reducedClosedSmoothPiece_range]
    rfl
  have hsource : ∀ y ∈ Ψ.source,
      y ∈ a3b4_cycleSupport Y.hom γ ↔ y ∈ Set.range (Point.map f) := by
    intro y hy
    obtain ⟨z, hzW, rfl⟩ := hy.2
    rw [hsupport]
    constructor
    · intro hzS
      obtain ⟨x, hx⟩ := (hrange z).mpr ⟨hzS, hzW⟩
      refine ⟨x, ?_⟩
      simpa only [f, Point.map, Category.assoc] using congrArg (Point.map j) hx
    · rintro ⟨x, hx⟩
      have hxz : Point.map g x = z := hj.injective (by
        simpa only [f, Point.map, Category.assoc] using hx)
      exact ((hrange z).mp ⟨x, hxz⟩).1
  obtain ⟨B, hB, hnormal⟩ :=
    a3b4a_gysin_smooth_dimension_normal_parameters A Y n c f γ Ψ hhol hAdim hsource
  let Q := Over.mk (reducedClosedSubschemeι R ≫ Z.hom)
  let k : Q ⟶ Z := Over.homMk (reducedClosedSubschemeι R) rfl
  letI : NoetherianSpace Q.left :=
    (reducedClosedSubschemeι R).isClosedEmbedding.isInducing.noetherianSpace
  letI : LocallyOfFiniteType Q.hom :=
    inferInstanceAs (LocallyOfFiniteType (reducedClosedSubschemeι R ≫ Z.hom))
  letI : QuasiCompact Q.hom := inferInstance
  letI : IsSeparated Q.hom :=
    inferInstanceAs (IsSeparated (reducedClosedSubschemeι R ≫ Z.hom))
  letI : IsLocallyNoetherian Q.left := LocallyOfFiniteType.isLocallyNoetherian Q.hom
  letI : IsNoetherian Q.left := {}
  letI : IsImmersion k.left := inferInstanceAs (IsImmersion (reducedClosedSubschemeι R))
  let D := (fun r => (Φ (Point.map (k ≫ j) r)).1) '' (Point.map (k ≫ j) ⁻¹' Φ.source)
  have hD : MeasureTheory.volume D = 0 :=
    a3b4a_gysin_algebraic_source_parameter_image_null Q Y (k ≫ j) n c
      (a3b4a_gysin_support_remainder_dimension_lt Z.hom S n hdim) Φ hΦ
  refine ⟨D ∪ B, MeasureTheory.measure_union_null hD hB, ?_⟩
  intro y hy hyU hys hnot
  let z := (ComplexPoint.openHomeomorph Y U).symm ⟨y, hyU⟩
  have hzy : Point.map j z = y :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph Y U).apply_symm_apply ⟨y, hyU⟩)
  have hzW : z ∈ W := by
    intro hzR
    have hzrange : z ∈ Set.range (Point.map k) := by
      rw [ComplexPoint.range_map_of_isImmersion_of_comm Z Q k]
      change z.underlying ∈ Set.range (reducedClosedSubschemeι R)
      rw [range_reducedClosedSubschemeι]
      exact hzR
    obtain ⟨r, hr⟩ := hzrange
    have hm : Point.map (k ≫ j) r = y := by
      calc
        _ = Point.map j (Point.map k r) := by simp only [Point.map, Category.assoc]
        _ = y := by rw [hr, hzy]
    apply hnot
    apply Or.inl
    refine ⟨r, ?_, congrArg (fun y => (Φ y).1) hm⟩
    change Point.map (k ≫ j) r ∈ Φ.source
    rwa [hm]
  have hyΨ : y ∈ Ψ.source := ⟨hy, z, hzW, hzy⟩
  obtain ⟨x, hx⟩ := (hsource y hyΨ).mp hys
  have hn : (Ψ (Point.map f x)).1 ∉ B := by
    change (Φ (Point.map f x)).1 ∉ B
    rw [hx]
    exact fun hb => hnot (Or.inr hb)
  have hr := hnormal x (hx.symm ▸ hyΨ) hn
  change ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = Point.map f x ∧
    HasFDerivAt (fun v' =>
      (C.chart (Φ.symm ((Φ (Point.map f x)).1, v' + (Φ (Point.map f x)).2))).2)
      (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 at hr
  simpa only [hx] using hr

end HodgeLean.Adapters
