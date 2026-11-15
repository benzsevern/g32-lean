import HodgeLean.Foundations.Program.SchoenTowerL1bActionSplitProofs

/-! # L1b orientation and action comparison pieces
The implication from local rotation and local homology signs supplies one shared
formal rescaling sign. The analytic comparison and sign constancy are open bodies.
HC no distance; AV milestone no distance.
-/
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
theorem s2v_l1b_action_label_sign
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
      ζ = Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (orderOf g : ℂ)) :=
  s2v_l1b_action_label_sign_aux S Y hdimY a ha1 hamul C eY hpointAction x g hrot hp ζ hζ ι hι hX hC hact

example
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
      ζ = Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (orderOf g : ℂ)) :=
  s2v_l1b_action_label_sign S Y hdimY a ha1 hamul C eY hpointAction x g hrot hp ζ hζ ι hι hX hC hact

/-- Local homology signs of a homeomorphism to an integral smooth curve agree
at every listed point. Empty lists allow either sign.
Source: Schoen (1988), Lemma 2.5, printed p. 15; Miranda, Algebraic Curves and
Riemann Surfaces, III.3, complex orientation and local cyclic actions. -/
theorem s2v_l1b_action_orientation_constant
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
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ j, ε j = s :=
  s2v_l1b_action_orientation_constant_aux Y hdimY M eY J y ε hε horient

example
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
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ j, ε j = s :=
  s2v_l1b_action_orientation_constant Y hdimY M eY J y ε hε horient

end HodgeLean.Foundations.Program
