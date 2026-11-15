import HodgeLean.Foundations.Program.SchoenTransferQ3OpenPairedSliceNormalization
import HodgeLean.Foundations.Program.SchoenTransferQ3NormalSliceDiagram
import HodgeLean.Foundations.Program.SchoenTransferQ3OpenSquareFibreLength

/-! Actual open tangential data calculate the original supported pullback. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Smooth tangential data on ambient opens calculate the original supported
pullback with the original map's unreduced point-fibre length. -/
theorem s4_q3_open_smooth_tangential_supported_pullback
    (X W X₀ W₀ C D T : Over (Spec ↧ℂ))
    (aX : X ⟶ X₀) (aW : W ⟶ W₀)
    [IsOpenImmersion aX.left] [IsOpenImmersion aW.left]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    (q₀ : X₀ ⟶ W₀)
    (i : C ⟶ X) (j : D ⟶ W) (f : C ⟶ D) (q : X ⟶ W) (h : W ⟶ T) (r d : ℕ)
    [SmoothOfRelativeDimension r C.hom] [SmoothOfRelativeDimension r D.hom]
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d W.hom]
    [SmoothOfRelativeDimension r T.hom]
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [IsFinite q.left] [Flat q.left] [Smooth h.left] [Smooth (q ≫ h).left]
    [Etale (i ≫ q ≫ h).left] [Etale (j ≫ h).left]
    (z : ComplexPoint C) (hsupport : i ≫ q = f ≫ j)

    (hambient : aX ≫ q₀ =
      q ≫ aW)
    (γ : AlgebraicCycle X₀.left ℚ) (δ : AlgebraicCycle W₀.left ℚ)
    (OX : Set (ComplexPoint X))
    (OW : Set (ComplexPoint W))
    (hOX : IsOpen OX) (hOW : IsOpen OW)
    (hxOX : Point.map i z ∈ OX) (hxOW : Point.map j (Point.map f z) ∈ OW)
    (hγ : ∀ y ∈ OX, Point.map (aX) y ∈
      a3b4_cycleSupport X₀.hom γ ↔ y ∈ Set.range (Point.map i))
    (hδ : ∀ y ∈ OW, Point.map (aW) y ∈
      a3b4_cycleSupport W₀.hom δ ↔ y ∈ Set.range (Point.map j))
    (hS : ∀ y, Point.map q₀ y ∈ a3b4_cycleSupport W₀.hom δ →
      y ∈ a3b4_cycleSupport X₀.hom γ)
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint W₀))
      (a3b4_cycleSupport W₀.hom δ)ᶜ) (2 * (d - r)))
    (hα : a3b4_IsCycleClass W₀.hom δ (d - r) α) :
    ∃ (E : OpenPartialHomeomorph (ComplexPoint X₀) ((Fin r → ℂ) × (Fin (d - r) → ℂ)))
      (hfE : ∀ y ∈ E.source, y ∈ a3b4_cycleSupport X₀.hom γ ↔ (E y).2 = 0),
      Point.map (i ≫ aX) z ∈ E.source ∧
      a3b4_IsHolChart X₀.hom E ∧
      ∃ (N : Set (ComplexPoint X₀)) (hNE : N ⊆ E.source), IsOpen N ∧
        Point.map (i ≫ aX) z ∈ N ∧
        relativeCohomologyMap ℚ (2 * (d - r))
          (a3b4_neighborhoodPairMap N (a3b4_cycleSupport X₀.hom γ))
          (relativeCohomologyMap ℚ (2 * (d - r))
            (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q₀))
              (a3b4_cycleSupport X₀.hom γ) (a3b4_cycleSupport W₀.hom δ) hS) α) =
          (a3b4_multiplicity W₀.hom δ
            (Point.map q₀ (Point.map (i ≫ aX) z)) *
            ((pointFibreLength q₀.left
              (Point.map (i ≫ aX) z).underlying).toNat : ℚ)) •
            chartNormalProjectionCoclass (Fin r → ℂ) (d - r) E
              (a3b4_cycleSupport X₀.hom γ) hfE N hNE := by
  let t := Point.map (j ≫ h) (Point.map f z)
  obtain ⟨P, Q, u, v, g, hsq, hcart, hP, hQ, hu, hv, hg, hflat, hsmP, hsmQ, hlength⟩ :=
    s4_q3_normal_slice_diagram q h t
  letI : IsClosedImmersion u.left := hu
  letI : IsClosedImmersion v.left := hv
  letI : IsFinite g.left := hg
  letI : Flat g.left := hflat
  letI : Smooth P.hom := hsmP
  letI : Smooth Q.hom := hsmQ
  letI : LocallyOfFiniteType P.hom := by rw [← Over.w u]; infer_instance
  letI : QuasiCompact P.hom := by rw [← Over.w u]; infer_instance
  letI : IsSeparated P.hom := by rw [← Over.w u]; infer_instance
  letI : LocallyOfFiniteType Q.hom := by rw [← Over.w v]; infer_instance
  letI : QuasiCompact Q.hom := by rw [← Over.w v]; infer_instance
  letI : IsSeparated Q.hom := by rw [← Over.w v]; infer_instance
  letI : T2Space (ComplexPoint P) := HodgeLean.Foundations.Analytic.f4_t2Space P
  letI : T2Space (ComplexPoint Q) := HodgeLean.Foundations.Analytic.f4_t2Space Q
  have ht : Point.map (i ≫ q ≫ h) z = t := by
    dsimp only [t]
    rw [← Category.assoc, hsupport, Category.assoc, Point.map_comp_apply]
  have hP' : IsPullback u.left P.hom (q ≫ h).left (Point.map (i ≫ q ≫ h) z).left := by
    rw [ht]; exact hP
  obtain ⟨xp, E, hfE, hxp, hxE, hE, N, hNE, hNo, hxN, hN⟩ :=
    s4_q3_open_paired_slice_supported_pullback P Q X W X₀ W₀ C D T aX aW q₀
      i j f q h u v g r d z hsupport hsq hP' hQ hambient
      γ δ OX OW hOX hOW hxOX hxOW hγ hδ hS α hα
  have hlen : pointFibreLength g.left xp.underlying =
      pointFibreLength q₀.left (Point.map (i ≫ aX) z).underlying := by
    calc
      _ = pointFibreLength q.left (u.left xp.underlying) := hlength _
      _ = pointFibreLength q₀.left (aX.left (u.left xp.underlying)) :=
        s4_q3_point_fibre_length_open_square aX.left aW.left q₀.left q.left
          (congrArg Over.Hom.left hambient) _
      _ = _ := congrArg (pointFibreLength q₀.left) (by
        rw [Point.underlying_map]
        exact congrArg aX.left (congrArg Point.underlying hxp))
  rw [hlen] at hN
  exact ⟨E, hfE, hxE, hE, N, hNE, hNo, hxN, hN⟩

end HodgeLean.Foundations.Program
