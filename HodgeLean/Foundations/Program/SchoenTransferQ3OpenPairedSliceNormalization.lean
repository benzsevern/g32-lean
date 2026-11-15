import HodgeLean.Foundations.Program.SchoenTransferQ3PairedSliceCharts
import HodgeLean.Foundations.Program.SchoenTransferQ3LocalSliceComparison
import HodgeLean.Foundations.Program.SchoenTransferQ3OpenChartTransport

/-! The original supported pullback calculated with charts on algebraic opens. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Actual slice charts on ambient opens calculate the original supported
pullback after holomorphic chart transport to the original spaces. -/
theorem s4_q3_open_paired_slice_supported_pullback
    (P Q X W X₀ W₀ C D T : Over (Spec ↧ℂ))
    (aX : X ⟶ X₀) (aW : W ⟶ W₀)
    [IsOpenImmersion aX.left] [IsOpenImmersion aW.left]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    (q₀ : X₀ ⟶ W₀)
    (i : C ⟶ X) (j : D ⟶ W) (f : C ⟶ D) (q : X ⟶ W) (h : W ⟶ T)
    (u : P ⟶ X) (v : Q ⟶ W) (g : P ⟶ Q) (r d : ℕ)
    [SmoothOfRelativeDimension r C.hom] [SmoothOfRelativeDimension r D.hom]
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d W.hom]
    [SmoothOfRelativeDimension r T.hom]
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    [Etale (i ≫ q ≫ h).left] [Etale (j ≫ h).left]
    (z : ComplexPoint C) (hsupport : i ≫ q = f ≫ j)
    (hslice : u ≫ q = g ≫ v)
    (hP : IsPullback u.left P.hom (q ≫ h).left (Point.map (i ≫ q ≫ h) z).left)
    (hQ : IsPullback v.left Q.hom h.left (Point.map (j ≫ h) (Point.map f z)).left)
    [Smooth P.hom] [Smooth Q.hom] [IsFinite g.left] [Flat g.left]
    [T1Space (ComplexPoint P)] [T1Space (ComplexPoint Q)]

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
    ∃ (xp : ComplexPoint P)
      (E : OpenPartialHomeomorph (ComplexPoint X₀) ((Fin r → ℂ) × (Fin (d - r) → ℂ)))
      (hfE : ∀ y ∈ E.source, y ∈ a3b4_cycleSupport X₀.hom γ ↔ (E y).2 = 0),
      Point.map u xp = Point.map i z ∧
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
            ((pointFibreLength g.left xp.underlying).toNat : ℚ)) •
            chartNormalProjectionCoclass (Fin r → ℂ) (d - r) E
              (a3b4_cycleSupport X₀.hom γ) hfE N hNE := by
  obtain ⟨xp, xq, eX, eW, sP, sQ, hxp, hxq, hg, hxX, hxW, hxP, hxQ,
    heX, heW, hsP, hsQ, hfX, hfW, hnP, hnQ, hP0, hQ0⟩ :=
    s4_q3_paired_cartesian_slice_point_charts P Q X W C D T i j f q h u v g r d
      z hsupport hslice hP hQ
  letI : Nonempty (ComplexPoint X) := ⟨Point.map i z⟩
  letI : Nonempty (ComplexPoint W) := ⟨Point.map j (Point.map f z)⟩
  let eXr := eX.restrOpen OX hOX
  let eWr := eW.restrOpen OW hOW
  have hxXr : Point.map i z ∈ eXr.source := ⟨hxX, hxOX⟩
  have hxWr : Point.map j (Point.map f z) ∈ eWr.source := ⟨hxW, hxOW⟩
  have heXr : a3b4_IsHolChart X.hom eXr :=
    ⟨fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
      (fun _ h => h.1) (heX.1 j),
      fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
        (fun _ h => h.1) (heX.2 j)⟩
  have heWr : a3b4_IsHolChart W.hom eWr :=
    ⟨fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
      (fun _ h => h.1) (heW.1 j),
      fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
        (fun _ h => h.1) (heW.2 j)⟩
  obtain ⟨E, hE, hsourceE, hvalueE⟩ :=
    s4_q3_holomorphic_chart_openImmersion_transport aX r (d - r) eXr heXr
  obtain ⟨F, hF, hsourceF, hvalueF⟩ :=
    s4_q3_holomorphic_chart_openImmersion_transport aW r (d - r) eWr heWr
  have hflatE : ∀ y ∈ E.source, y ∈ a3b4_cycleSupport X₀.hom γ ↔ (E y).2 = 0 := by
    intro y hy
    rw [hsourceE] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hvalueE]
    exact (hγ y hy.2).trans (hfX y hy.1)
  have hflatF : ∀ y ∈ F.source, y ∈ a3b4_cycleSupport W₀.hom δ ↔ (F y).2 = 0 := by
    intro y hy
    rw [hsourceF] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hvalueF]
    exact (hδ y hy.2).trans (hfW y hy.1)
  have hxE : Point.map aX (Point.map i z) ∈ E.source := by
    rw [hsourceE]; exact ⟨_, hxXr, rfl⟩
  have hxF : Point.map aW (Point.map j (Point.map f z)) ∈ F.source := by
    rw [hsourceF]; exact ⟨_, hxWr, rfl⟩
  have hxδ : Point.map aW (Point.map j (Point.map f z)) ∈ a3b4_cycleSupport W₀.hom δ :=
    (hδ _ hxOW).mpr (Set.mem_range_self _)
  have himage : Point.map q₀ (Point.map aX (Point.map i z)) =
      Point.map aW (Point.map j (Point.map f z)) := by
    calc
      _ = Point.map aW (Point.map q (Point.map i z)) := by
        rw [← Point.map_comp_apply aX q₀, hambient, Point.map_comp_apply]
      _ = _ := congrArg (Point.map aW) (by
        rw [← Point.map_comp_apply i q, hsupport, Point.map_comp_apply])
  obtain ⟨VZ, hVZ, hVZo, hzV, hnorm⟩ :=
    hα r F hflatF (Point.map aW (Point.map j (Point.map f z))) hxF hxδ hF
  have hcomm : ∀ y, Point.map q₀ (Point.map (u ≫ aX) y) =
      Point.map (v ≫ aW) (Point.map g y) := by
    intro y
    rw [← Point.map_comp_apply, Category.assoc, hambient, ← Category.assoc,
      hslice, Category.assoc, Point.map_comp_apply]
  have hxE' : Point.map (u ≫ aX) xp ∈ E.source := by
    rw [Point.map_comp_apply, hxp]; exact hxE
  have hxE0 : (E (Point.map (u ≫ aX) xp)).2 = 0 := by
    rw [Point.map_comp_apply, hvalueE, hxp]
    exact (hfX _ hxX).mp (Set.mem_range_self _)
  have hxVZ : Point.map (v ≫ aW) (Point.map g xp) ∈ VZ := by
    rw [hg, Point.map_comp_apply, hxq]; exact hzV
  have hnorm' : relativeCohomologyMap ℚ (2 * (d - r))
      (a3b4_neighborhoodPairMap VZ (a3b4_cycleSupport W₀.hom δ)) α =
      a3b4_multiplicity W₀.hom δ (Point.map q₀ (Point.map aX (Point.map i z))) •
        chartNormalProjectionCoclass (Fin r → ℂ) (d - r) F
          (a3b4_cycleSupport W₀.hom δ) hflatF VZ hVZ := by
    rw [himage]; exact hnorm
  obtain ⟨N, hNE, hNo, hxN, hN⟩ :=
    s4_q3_local_ambient_finite_flat_slice_comparison (Fin r → ℂ) (Fin r → ℂ) (d - r)
      g (Point.continuousMap q₀) (Point.continuousMap (u ≫ aX))
      (Point.continuousMap (v ≫ aW)) hcomm
      (a3b4_cycleSupport X₀.hom γ) (a3b4_cycleSupport W₀.hom δ) hS
      E F hflatE hflatF sP sQ hsP hsQ xp hxP (hg.symm ▸ hxQ) hP0 (hg.symm ▸ hQ0)
      hxE' hxE0 VZ hVZ hVZo hxVZ
      (fun y _ => by
        change (E (Point.map (u ≫ aX) y)).2 = (sP y).2
        rw [Point.map_comp_apply, hvalueE]; exact (hnP y).symm)
      (fun y _ => by
        change (F (Point.map (v ≫ aW) y)).2 = (sQ y).2
        rw [Point.map_comp_apply, hvalueF]; exact (hnQ y).symm) α _ hnorm'
  have hmarked : Point.map (u ≫ aX) xp = Point.map (i ≫ aX) z := by
    rw [Point.map_comp_apply, hxp, Point.map_comp_apply]
  have hxN' : Point.map (i ≫ aX) z ∈ N := by
    change Point.map (u ≫ aX) xp ∈ N at hxN
    rwa [hmarked] at hxN
  refine ⟨xp, E, hflatE, hxp, ?_, hE, N, hNE, hNo, hxN', ?_⟩
  · rw [Point.map_comp_apply]; exact hxE
  · exact hN

end HodgeLean.Foundations.Program
