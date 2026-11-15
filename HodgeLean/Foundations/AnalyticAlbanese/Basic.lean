import HodgeLean.Foundations.AnalyticAlbanese.Proofs

/-! # Analytic Albanese: universality and algebraic descent

This first stage separates analytic universality from denominator and cohomology realization.
HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 10000

noncomputable section
open scoped TensorProduct ContDiff CategoryTheory.MonObj
open Manifold CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
open CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.AnalyticAlbanese

/-- The pointed holomorphic map determines a unique complex-linear period lift, preserving the actual lattices.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §11.1 (universal property of the Jacobian); Forster, *Lectures on Riemann Surfaces*, §21.
HC no distance; AV milestone no distance. -/
theorem period_lift (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
    [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (Μ : Type) [AddCommGroup Μ] [Module.Finite ℤ Μ] [Module.Free ℤ Μ]
    (G : Submodule ℂ (ℂ ⊗[ℤ] Μ)) (hG : b2_IsWeightOne Μ G)
    [DiscreteTopology (b2_latticeMap Μ G).range]
    (p₀ : C) (f : C → b2_torus Μ G)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V Μ G) ω f) (hbase : f p₀ = 0) :
    ∃! L : ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G),
      (∀ l : b3_periodLattice E C,
        L (b2_latticeMap _ (b3_periodF E C) l) ∈ (b2_latticeMap Μ G).range) ∧
      ∀ (path : ℝ → C), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 path →
        ∀ v : ℂ ⊗[ℤ] b3_periodLattice E C,
          b3_cplxPeriod E C v = b3_pathPeriod E C path →
          (QuotientAddGroup.mk (L (Submodule.Quotient.mk v)) : b2_torus Μ G) =
            f (path 1) - f (path 0) := period_lift_aux E C hE Μ G hG p₀ f hf hbase

set_option maxHeartbeats 1000 in
example (l : b3_periodLattice b3_EllipticModel b3_Elliptic) :
    b3_cplxPeriod b3_EllipticModel b3_Elliptic ((1 : ℂ) ⊗ₜ[ℤ] l) b3A_dz =
      (l : b3_HolForm b3_EllipticModel b3_Elliptic → ℂ) b3A_dz := by
  simp only [b3_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

/-- The actual quotient descent is holomorphic and retains its representative equation.
Source: Birkenhake–Lange, §1.2 (analytic representation of a torus homomorphism).
HC no distance; AV milestone no distance. -/
theorem descent_holomorphic (Λ Μ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [AddCommGroup Μ] [Module.Finite ℤ Μ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (G : Submodule ℂ (ℂ ⊗[ℤ] Μ))
    [DiscreteTopology (b2_latticeMap Λ F).range]
    [DiscreteTopology (b2_latticeMap Μ G).range]
    (L : ((ℂ ⊗[ℤ] Λ) ⧸ F) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hL : ∀ l : Λ, L (b2_latticeMap Λ F l) ∈ (b2_latticeMap Μ G).range) :
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, b5_V Μ G) ω (descend F G L hL) ∧
      ∀ v, descend F G L hL (QuotientAddGroup.mk v) = QuotientAddGroup.mk (L v) := descent_holomorphic_aux Λ Μ F G L hL

set_option maxHeartbeats 1000 in
example {Λ Μ : Type} [AddCommGroup Λ] [AddCommGroup Μ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (G : Submodule ℂ (ℂ ⊗[ℤ] Μ))
    (L : ((ℂ ⊗[ℤ] Λ) ⧸ F) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hL : ∀ l, L (b2_latticeMap Λ F l) ∈ (b2_latticeMap Μ G).range)
    (v : (ℂ ⊗[ℤ] Λ) ⧸ F) :
    descend F G L hL (QuotientAddGroup.mk v) = QuotientAddGroup.mk (L v) := rfl

/-- The descended lift is the unique holomorphic additive factor of the pointed map.
Source: Birkenhake–Lange, §11.1 (Albanese property); Forster, §21.
HC no distance; AV milestone no distance. -/
theorem factorization_unique (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
    [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (Μ : Type) [AddCommGroup Μ] [Module.Finite ℤ Μ] [Module.Free ℤ Μ]
    (G : Submodule ℂ (ℂ ⊗[ℤ] Μ)) (hG : b2_IsWeightOne Μ G)
    [DiscreteTopology (b2_latticeMap Μ G).range]
    (p₀ : C) (f : C → b2_torus Μ G)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V Μ G) ω f) (hbase : f p₀ = 0)
    (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj)
    (L : ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hL : ∀ l : b3_periodLattice E C,
      L (b2_latticeMap _ (b3_periodF E C) l) ∈ (b2_latticeMap Μ G).range)
    (hpath : ∀ (path : ℝ → C), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 path →
        ∀ v : ℂ ⊗[ℤ] b3_periodLattice E C,
          b3_cplxPeriod E C v = b3_pathPeriod E C path →
          (QuotientAddGroup.mk (L (Submodule.Quotient.mk v)) : b2_torus Μ G) =
            f (path 1) - f (path 0)) :
    (∀ p, descend (b3_periodF E C) G L hL (aj p) = f p) ∧
      ∀ H : b3_Jacobian E C →+ b2_torus Μ G,
        ContMDiff 𝓘(ℂ, b5_V (b3_periodLattice E C) (b3_periodF E C))
          𝓘(ℂ, b5_V Μ G) ω H →
        (∀ p, H (aj p) = f p) → H = descend (b3_periodF E C) G L hL := factorization_unique_aux E C hE Μ G hG p₀ f hf hbase aj haj L hL hpath

set_option maxHeartbeats 1000 in
example (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (haj : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj)
    (H K : b3_Jacobian b3_EllipticModel b3_Elliptic → b3_Elliptic)
    (h : ∀ p, H (aj p) = K (aj p)) : H = K := by
  funext j
  obtain ⟨p, rfl⟩ := (b3A_elliptic_abelJacobi_bijective aj haj).2 j
  exact h p

/-- Algebraize the specified cross-variety descent on the actual B5 models, retaining its theta equation and group law.
Source: Serre, *Géométrie algébrique et géométrie analytique* (1956), §3, Proposition 13; Birkenhake–Lange, §1.2; `gagam_algebraize`.
HC no distance; AV milestone no distance. -/
theorem algebraize_descent (Λ Μ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    [AddCommGroup Μ] [Module.Finite ℤ Μ] [Module.Free ℤ Μ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (G : Submodule ℂ (ℂ ⊗[ℤ] Μ))
    (hF : b2_IsWeightOne Λ F) (hG : b2_IsWeightOne Μ G)
    (Q : LinearMap.BilinForm ℤ Λ) (R : LinearMap.BilinForm ℤ Μ)
    (hQ : b2_IsRiemannForm Λ F Q) (hR : b2_IsRiemannForm Μ G R)
    (L : ((ℂ ⊗[ℤ] Λ) ⧸ F) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hL : ∀ l : Λ, L (b2_latticeMap Λ F l) ∈ (b2_latticeMap Μ G).range) :
    letI := b5_groupObj Λ F hF Q hQ
    letI := b5_groupObj Μ G hG R hR
    ∃! a : b5_model Λ F hF Q ⟶ b5_model Μ G hG R,
      IsMonHom a ∧ ∀ t,
        Point.map a (b5_theta Λ F hF Q hQ t) =
          b5_theta Μ G hG R hR (descend F G L hL t) := algebraize_descent_aux Λ Μ F G hF hG Q R hQ hR L hL

set_option maxHeartbeats 5000 in
example (t : b3_Elliptic) :
    let X := b5_model (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne b2_stdForm
    letI := b5_groupObj (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne
      b2_stdForm b2_std_isRiemannForm
    let θ := b5_theta (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne
      b2_stdForm b2_std_isRiemannForm
    Point.map ((𝟙 X) * (𝟙 X)) (θ t) = θ (t + t) := by
  letI := b5_groupObj (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne
    b2_stdForm b2_std_isRiemannForm
  have hg := (b5_group (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne
    b2_stdForm b2_std_isRiemannForm).2.1 t t
  change (b5_theta (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne
    b2_stdForm b2_std_isRiemannForm t) ≫ ((𝟙 _) * (𝟙 _)) = _
  simp only [MonObj.comp_mul, Category.comp_id]
  exact hg.symm

/-- Faithful complex-point evaluation reflects equality and the group law between distinct smooth projective models.
Source: Mumford, *Abelian Varieties*, §1 (morphisms and complex points); Mathlib `AlgebraicGeometry.ext_of_apply_eq` in `AlgebraicGeometry/AlgClosed/Basic.lean` (reduced source and separated target).
HC no distance; AV milestone no distance. -/
theorem faithful_group_reflection (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    (∀ a b : X ⟶ Y, Point.map a = Point.map b → a = b) ∧
      ∀ a : X ⟶ Y, Point.map a (1 : ComplexPoint X) = (1 : ComplexPoint Y) →
        (∀ x y : ComplexPoint X, Point.map a (x * y) = Point.map a x * Point.map a y) →
        IsMonHom a := faithful_group_reflection_aux X Y

set_option maxHeartbeats 1000 in
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] :
    IsMonHom ((𝟙 X) * (𝟙 X)) := by
  rw [Hom.mul_def]
  infer_instance

end HodgeLean.Foundations.AnalyticAlbanese
