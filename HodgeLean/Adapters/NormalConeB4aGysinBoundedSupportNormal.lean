import HodgeLean.Adapters.NormalConeB4aGysinSmoothDimensionNormal
import HodgeLean.Adapters.NormalConeB4aGysinRemainderProjectionNull

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual algebraic cycle support of bounded dimension has normal charts
with identity vertical derivatives over every parameter outside a null set. -/
theorem a3b4a_gysin_bounded_support_normal_parameters
    (Y : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (γ : AlgebraicCycle Y.left ℚ) (S : Closeds Y.left) (n c : ℕ)
    (hdim : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n : ℕ))
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ)
    (hS : ∀ y ∈ Φ.source, y ∈ a3b4_cycleSupport Y.hom γ ↔ y.underlying ∈ S) :
    ∃ B : Set (Fin n → ℂ), MeasureTheory.volume B = 0 ∧
      ∀ y : ComplexPoint Y, y ∈ Φ.source → y ∈ a3b4_cycleSupport Y.hom γ →
        (Φ y).1 ∉ B →
        ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = y ∧
          HasFDerivAt (fun v' =>
            (C.chart (Φ.symm ((Φ y).1, v' + (Φ y).2))).2)
            (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  let R := reducedClosedSingularRemainder Y.hom S
  let W : Set (ComplexPoint Y) := {y | y.underlying ∉ R}
  have hW : IsOpen W :=
    (R.isClosed.preimage (ComplexPoint.continuous_underlying_to_zariski Y)).isOpen_compl
  let Ψ := Φ.restrOpen W hW
  let A := Over.mk (reducedClosedSmoothPieceι Y.hom S ≫ Y.hom)
  let f : A ⟶ Y := Over.homMk (reducedClosedSmoothPieceι Y.hom S) rfl
  letI : NoetherianSpace (reducedClosedSubscheme S) :=
    (reducedClosedSubschemeι S).isClosedEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace (reducedClosedSmoothPiece Y.hom S) :=
    (reducedClosedStructureMap Y.hom S).smoothLocus.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace A.left :=
    inferInstanceAs (NoetherianSpace (reducedClosedSmoothPiece Y.hom S))
  letI : Smooth A.hom :=
    inferInstanceAs (Smooth (reducedClosedSmoothPieceι Y.hom S ≫ Y.hom))
  letI : LocallyOfFiniteType A.hom :=
    inferInstanceAs (LocallyOfFiniteType (reducedClosedSmoothPieceι Y.hom S ≫ Y.hom))
  letI : QuasiCompact A.hom := inferInstance
  letI : IsSeparated A.hom :=
    inferInstanceAs (IsSeparated (reducedClosedSmoothPieceι Y.hom S ≫ Y.hom))
  letI : IsImmersion f.left :=
    inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι Y.hom S))
  have hAdim : topologicalKrullDim A.left ≤ (n : ℕ) :=
    (reducedClosedStructureMap Y.hom S).smoothLocus.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hhol : a3b4_IsHolChart Y.hom Ψ := by
    constructor
    · intro k
      exact anrem_isHolFun_restrict (f4_analytification Y) (fun _ hz => hz.1) (hΦ.1 k)
    · intro k
      exact anrem_isHolFun_restrict (f4_analytification Y) (fun _ hz => hz.1) (hΦ.2 k)
  have hsource : ∀ y ∈ Ψ.source,
      y ∈ a3b4_cycleSupport Y.hom γ ↔ y ∈ Set.range (Point.map f) := by
    intro y hy
    rw [hS y hy.1, ComplexPoint.range_map_of_isImmersion_of_comm Y A f]
    change y.underlying ∈ S ↔ y.underlying ∈ Set.range (reducedClosedSmoothPieceι Y.hom S)
    rw [reducedClosedSmoothPiece_range]
    exact ⟨fun hs => ⟨hs, hy.2⟩, fun hs => hs.1⟩
  obtain ⟨B, hB, hnormal⟩ :=
    a3b4a_gysin_smooth_dimension_normal_parameters A Y n c f γ Ψ hhol hAdim hsource
  let D := (fun y : ComplexPoint Y => (Φ y).1) ''
    {y | y ∈ Φ.source ∧ y.underlying ∈ R}
  have hD : MeasureTheory.volume D = 0 :=
    a3b4a_gysin_support_remainder_parameter_image_null Y S n c hdim Φ hΦ
  refine ⟨D ∪ B, MeasureTheory.measure_union_null hD hB, ?_⟩
  intro y hy hys hnot
  have hyW : y ∈ W := by
    intro hyR
    exact hnot (Or.inl ⟨y, ⟨hy, hyR⟩, rfl⟩)
  have hyΨ : y ∈ Ψ.source := ⟨hy, hyW⟩
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
