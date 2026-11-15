import HodgeLean.Foundations.Program.SchoenTowerL1bActionSplitDefs
import HodgeLean.Foundations.Program.SchoenTowerL1bOrientationGlobal
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationCurveAction
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationFixedPoint
import HodgeLean.Foundations.Program.SchoenTowerL1bActionLocalRotation

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 200000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The sign of the map on integral local homology identifies the scalar of
any scalar-preserving parameter expansion at a rotation point.
Source: Schoen (1988), Lemma 2.5, printed p. 15; Miranda, Algebraic Curves and
Riemann Surfaces, III.3, Proposition 3.1. -/
theorem s2v_l1b_action_label_sign_aux
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (x : rsq_Quot S.χ.ker C) (g : S.H ⧸ S.χ.ker)
    (hrot : b4_IsRotGen ℂ x g)
    (hp : (a g).left (eY x).underlying = (eY x).underlying)
    (ζ : ℂ) (hζ : ζ ^ orderOf g = 1)
    (ι : Y.left.presheaf.stalk (eY x).underlying →+* PowerSeries ℂ)
    (hι : Function.Injective ι) (hX : ∃ u, ι u = PowerSeries.X)
    (hC : ∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC (eY x).underlying c) =
      PowerSeries.C c)
    (hact : ∀ v, ι (s2e_fixed_point_stalkPullback Y.left (a g).left
      (eY x).underlying hp v) = PowerSeries.rescale ζ (ι v)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      relativeHomologyMap ℤ 2
        (imagePointPairMap (TopCat.ofHom ⟨eY, eY.continuous⟩) eY.injective x)
        (b6m_surfaceLocalClass ℤ x) =
          ε • s2v_l1b_action_curveLocalClass Y hdimY (eY x) ∧
      ζ = Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (orderOf g : ℂ)) := by
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    simpa only [hdimY] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Y.left) Y.hom)
  obtain ⟨ε, hε, horient⟩ := s2v_l1b_action_local_sign_exists Y hdimY _ eY x
  refine ⟨ε, hε, horient, ?_⟩
  have hfixed : Point.map (a g) (eY x) = eY x := by
    rw [hpointAction, hrot.1]
  exact (s2v_l1b_action_scalar_coordinate_derivative Y (eY x) (a g) hp hfixed
    ι hX hC ζ hact).trans
      (s2v_l1b_action_local_rotation_sign Y hdimY _ _ eY (a g) g
        (hpointAction g) x hrot ε hε horient)

/-- Local homology signs of a homeomorphism to an integral smooth curve agree
at every listed point. Empty lists allow either sign.
Source: Schoen (1988), Lemma 2.5, printed p. 15; Miranda, Algebraic Curves and
Riemann Surfaces, III.3, complex orientation and local cyclic actions. -/
theorem s2v_l1b_action_orientation_constant_aux
    (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M]
    (eY : M ≃ₜ ComplexPoint Y)
    (J : Type) (y : J → M) (ε : J → ℤ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (horient : ∀ j, relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨eY, eY.continuous⟩) eY.injective (y j))
      (b6m_surfaceLocalClass ℤ (y j)) =
        ε j • s2v_l1b_action_curveLocalClass Y hdimY (eY (y j))) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ j, ε j = s := by
  classical
  letI : ConnectedSpace (ComplexPoint Y) := ComplexPoint.connectedSpace Y
  letI : T2Space M := eY.symm.t2Space
  letI : CompactSpace M := eY.symm.compactSpace
  obtain ⟨u, hu⟩ := b6m_surface_absoluteOrientation ℤ (C := M)
  obtain ⟨w, hw, hgen⟩ := s2v_l1b_native_generator ℤ _ hdimY
    (N := ComplexPoint Y)
  have hw' : ∀ p, (relativeHomologyProjection ℤ (pointComplementPair p) 2).hom w =
      s2v_l1b_action_curveLocalClass Y hdimY p := hw
  have hsurj : Function.Surjective (fun r : ℤ => r • w) := by
    intro z
    obtain ⟨r, hr⟩ := hgen.2 z
    exact ⟨r, (int_smul_eq_zsmul _ _ _).symm.trans hr⟩
  let f := TopCat.ofHom ⟨eY, eY.continuous⟩
  obtain ⟨r, hr⟩ := hsurj (homologyMap ℤ 2 f u)
  have heq (j : J) : ε j = r := by
    have h := s2v_l1b_projection_map ℤ
      (imagePointPairMap f eY.injective (y j)) 2 u
    rw [hu] at h
    change relativeHomologyMap ℤ 2 (imagePointPairMap f eY.injective (y j))
      (b6m_surfaceLocalClass ℤ (y j)) =
        (relativeHomologyProjection ℤ (pointComplementPair (eY (y j))) 2).hom
          (homologyMap ℤ 2 f u) at h
    rw [← hr, map_zsmul, hw', horient j] at h
    have hinj : Function.Injective (fun n : ℤ =>
        n • s2v_l1b_action_curveLocalClass Y hdimY (eY (y j))) := by
      have hlocal := (s2v_l1b_native_local_generator ℤ _ hdimY (eY (y j))).1
      intro a b hab
      apply hlocal
      exact (int_smul_eq_zsmul (ModuleCat.isModule _) a _).trans
        (hab.trans (int_smul_eq_zsmul (ModuleCat.isModule _) b _).symm)
    exact hinj h
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨1, Or.inl rfl, fun j => isEmptyElim j⟩
  · let j := Classical.choice hJ
    exact ⟨r, (heq j) ▸ hε j, heq⟩

end HodgeLean.Foundations.Program
