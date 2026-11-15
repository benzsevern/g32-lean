import HodgeLean.Foundations.AnalyticAlbanese.Defs
import HodgeLean.Foundations.AnalyticAlbanese.PathFactorization
import HodgeLean.Foundations.AnalyticAlbanese.LinearUniqueness
import HodgeLean.Foundations.AnalyticAlbanese.AnalyticRepresentation

/-! # Analytic Albanese: analytic universality

This first stage separates analytic universality from denominator and cohomology realization.
HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000

noncomputable section
open scoped TensorProduct ContDiff CategoryTheory.MonObj
open Filter Topology Manifold CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
open CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.AnalyticAlbanese

/-- The pointed holomorphic map determines a unique complex-linear period lift, preserving the actual lattices.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §11.1 (universal property of the Jacobian); Forster, *Lectures on Riemann Surfaces*, §21.
HC no distance; AV milestone no distance. -/
theorem period_lift_aux (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
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
            f (path 1) - f (path 0) := by
  refine ⟨coordinateLift G f hf,
    ⟨coordinateLift_lattice G f hf, coordinateLift_increment G f hf⟩, ?_⟩
  intro K hK
  apply sub_eq_zero.mp
  apply linear_eq_zero_of_path_classes E C hE Μ G (K - coordinateLift G f hf)
  intro path hpathSmooth v hv
  change (QuotientAddGroup.mk (K (Submodule.Quotient.mk v) -
    coordinateLift G f hf (Submodule.Quotient.mk v)) : b2_torus Μ G) = 0
  rw [QuotientAddGroup.mk_sub, hK.2 path hpathSmooth v hv, coordinateLift_increment G f hf path hpathSmooth v hv,
    sub_self]

set_option maxHeartbeats 1000 in
example (l : b3_periodLattice b3_EllipticModel b3_Elliptic) :
    b3_cplxPeriod b3_EllipticModel b3_Elliptic ((1 : ℂ) ⊗ₜ[ℤ] l) b3A_dz =
      (l : b3_HolForm b3_EllipticModel b3_Elliptic → ℂ) b3A_dz := by
  simp only [b3_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

/-- The actual quotient descent is holomorphic and retains its representative equation.
Source: Birkenhake–Lange, §1.2 (analytic representation of a torus homomorphism).
HC no distance; AV milestone no distance. -/
theorem descent_holomorphic_aux (Λ Μ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [AddCommGroup Μ] [Module.Finite ℤ Μ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (G : Submodule ℂ (ℂ ⊗[ℤ] Μ))
    [DiscreteTopology (b2_latticeMap Λ F).range]
    [DiscreteTopology (b2_latticeMap Μ G).range]
    (L : ((ℂ ⊗[ℤ] Λ) ⧸ F) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hL : ∀ l : Λ, L (b2_latticeMap Λ F l) ∈ (b2_latticeMap Μ G).range) :
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, b5_V Μ G) ω (descend F G L hL) ∧
      ∀ v, descend F G L hL (QuotientAddGroup.mk v) = QuotientAddGroup.mk (L v) := by
  have hc : Continuous (descend F G L hL) := by
    refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact continuous_quotient_mk'.comp (IsModuleTopology.continuous_of_linearMap L)
  refine ⟨?_, fun _ ↦ rfl⟩
  intro t
  rw [contMDiffAt_iff]
  refine ⟨hc.continuousAt, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id,
    contDiffWithinAt_univ]
  set A : (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) →ₗ[ℂ]
      (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Μ) ⧸ G)) → ℂ) :=
    (b2_coord _).toLinearMap ∘ₗ L ∘ₗ (b2_coord _).symm.toLinearMap
  set f : (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) → (ℂ ⊗[ℤ] Μ) ⧸ G :=
    fun y ↦ L ((b2_coordHomeomorph Λ F).symm y)
  have hf : Continuous f := (IsModuleTopology.continuous_of_linearMap
    L).comp (b2_coordHomeomorph Λ F).symm.continuous
  set y₀ := chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) t t
  have hsymm : ∀ y, (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) t).symm y =
      QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm y) :=
    b2t_torusChart_symm_apply F t
  have hy₀ : (QuotientAddGroup.mk (f y₀) : b2_torus Μ G) =
      descend F G L hL t := by
    have : (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) t).symm y₀ = t :=
      (chartAt _ t).left_inv (mem_chart_source _ t)
    rw [hsymm] at this
    rw [← this]
    rfl
  obtain ⟨a, ha⟩ := b2t_torusChart_eventually G (descend F G L hL t) hf.continuousAt
    (by rw [hy₀]; exact mem_chart_source _ _)
  have : (fun y ↦ A y + a) =ᶠ[𝓝 y₀] (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Μ) ⧸ G)) → ℂ)
      (descend F G L hL t) ∘ descend F G L hL ∘
        (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) t).symm) := by
    filter_upwards [ha] with z hz
    simp only [Function.comp_apply, hsymm]
    erw [hz]
    rfl
  exact ((LinearMap.toContinuousLinearMap A).contDiff.contDiffAt.add
    contDiffAt_const).congr_of_eventuallyEq this.symm

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
theorem factorization_unique_aux (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
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
        (∀ p, H (aj p) = f p) → H = descend (b3_periodF E C) G L hL := by
  have heval := factor_evaluation_of_paths E C Μ G p₀ f hbase aj haj L hL hpath
  refine ⟨heval, ?_⟩
  intro H hH hfactor
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_torus_compactSpace (b3_periodF E C) (b3_isWeightOne hE)
  letI : ConnectedSpace (((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) :=
    (b2_coordHomeomorph (b3_periodLattice E C) (b3_periodF E C)).symm.surjective.connectedSpace
      (b2_coordHomeomorph (b3_periodLattice E C) (b3_periodF E C)).symm.continuous
  letI : ConnectedSpace (b3_Jacobian E C) :=
    (QuotientAddGroup.mk_surjective : Function.Surjective
      (QuotientAddGroup.mk : ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) →
        b3_Jacobian E C)).connectedSpace continuous_quotient_mk'
  let M := analyticLinear (b3_periodF E C) G H hH
  have hM : M = L := by
    apply sub_eq_zero.mp
    apply linear_eq_zero_of_path_classes E C hE Μ G (M - L)
    intro path hpathSmooth v hv
    obtain ⟨w, hw, hajw⟩ := haj.2 path hpathSmooth
    have hq : Submodule.Quotient.mk (p := b3_periodF E C) v =
        Submodule.Quotient.mk w :=
      (Submodule.Quotient.eq _).2 (LinearMap.sub_mem_ker_iff.2 (hv.trans hw.symm))
    have hmv : (QuotientAddGroup.mk (M (Submodule.Quotient.mk v)) : b2_torus Μ G) =
        f (path 1) - f (path 0) := by
      rw [← analyticLinear_mk (b3_periodF E C) G H hH, hq, ← hajw, map_sub, hfactor, hfactor]
    change (QuotientAddGroup.mk (M (Submodule.Quotient.mk v) - L (Submodule.Quotient.mk v)) :
      b2_torus Μ G) = 0
    rw [QuotientAddGroup.mk_sub, hmv, hpath path hpathSmooth v hv, sub_self]
  apply AddMonoidHom.ext
  intro t
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  change H (QuotientAddGroup.mk w) = QuotientAddGroup.mk (L w)
  rw [analyticLinear_mk (b3_periodF E C) G H hH]
  exact congrArg QuotientAddGroup.mk (LinearMap.congr_fun hM w)

set_option maxHeartbeats 1000 in
example (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (haj : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj)
    (H K : b3_Jacobian b3_EllipticModel b3_Elliptic → b3_Elliptic)
    (h : ∀ p, H (aj p) = K (aj p)) : H = K := by
  funext j
  obtain ⟨p, rfl⟩ := (b3A_elliptic_abelJacobi_bijective aj haj).2 j
  exact h p

/-- Faithful complex-point evaluation reflects equality and the group law between distinct smooth projective models.
Source: Mumford, *Abelian Varieties*, §1 (morphisms and complex points); Mathlib `AlgebraicGeometry.ext_of_apply_eq` in `AlgebraicGeometry/AlgClosed/Basic.lean` (reduced source and separated target).
HC no distance; AV milestone no distance. -/
theorem faithful_group_reflection_aux (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    (∀ a b : X ⟶ Y, Point.map a = Point.map b → a = b) ∧
      ∀ a : X ⟶ Y, Point.map a (1 : ComplexPoint X) = (1 : ComplexPoint Y) →
        (∀ x y : ComplexPoint X, Point.map a (x * y) = Point.map a x * Point.map a y) →
        IsMonHom a := by
  refine ⟨fun _ _ h ↦ b55_hom_ext h, ?_⟩
  intro a h1 hmul
  let s : MonoidalCategory.tensorUnit (Over (Spec ↧ℂ)) ⟶ Over.mk (𝟙 (Spec ↧ℂ)) :=
    Over.homMk (MonoidalCategory.tensorUnit (Over (Spec ↧ℂ))).hom (by simp)
  have hs : s ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
    CartesianMonoidalCategory.toUnit_unique _ _
  have : IsIntegral (MonoidalCategory.tensorObj X X).left :=
    complexSelfProductIntegral_of_isIntegral X
  have : LocallyOfFiniteType (MonoidalCategory.tensorObj X X).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst X.hom X.hom ≫ X.hom)
    infer_instance
  refine ⟨?_, ?_⟩
  · have h1' : (CartesianMonoidalCategory.toUnit _ ≫ η[X]) ≫ a =
        CartesianMonoidalCategory.toUnit _ ≫ η[Y] := h1
    calc η[X] ≫ a = s ≫ (CartesianMonoidalCategory.toUnit _ ≫ η[X]) ≫ a := by
          rw [Category.assoc, ← Category.assoc s, hs, Category.id_comp]
      _ = η[Y] := by rw [h1', ← Category.assoc, hs, Category.id_comp]
  · apply b55_hom_ext
    funext z
    change z ≫ μ ≫ a = z ≫ MonoidalCategory.tensorHom a a ≫ μ
    have hz : z = CartesianMonoidalCategory.lift (z ≫ CartesianMonoidalCategory.fst X X)
        (z ≫ CartesianMonoidalCategory.snd X X) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hz, ← Category.assoc, ← Category.assoc, CartesianMonoidalCategory.lift_map,
      ← Hom.mul_def, ← Hom.mul_def]
    exact hmul _ _


/-- Algebraize the specified cross-variety descent on the actual B5 models, retaining its theta equation and group law.
Source: Serre, *Géométrie algébrique et géométrie analytique* (1956), §3, Proposition 13; Birkenhake–Lange, §1.2; `gagam_algebraize`.
HC no distance; AV milestone no distance. -/
theorem algebraize_descent_aux (Λ Μ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
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
          b5_theta Μ G hG R hR (descend F G L hL t) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI := b5_groupObj Μ G hG R hR
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Μ G hG R hR
  letI := b5_projective_aux Μ G hG R hR
  letI : IsIntegral (b5_model Μ G hG R).left := b5_integral_aux Μ G hG R hR
  letI := b2_latticeMap_discrete F hF
  letI := b2_latticeMap_discrete G hG
  let e := b5_thetaEquiv Λ F hF Q hQ
  let d := b5_thetaEquiv Μ G hG R hR
  let D := descend F G L hL
  have hhol := (b5_theta_holomorphicFunctions Μ G hG R hR).1.comp
    ((descent_holomorphic_aux Λ Μ F G L hL).1.comp
      (b5_theta_holomorphicFunctions Λ F hF Q hQ).2.1)
  obtain ⟨a, ha⟩ := HodgeLean.Adapters.gagam_algebraize
    (b5_model Λ F hF Q) (b5_model Μ G hG R) (fun p ↦ d (D (e.symm p))) hhol
  have heq : ∀ t, Point.map a (e t) = d (D t) := by
    intro t
    rw [ha]
    change d (D (e.symm (e t))) = d (D t)
    rw [e.symm_apply_apply]
  have gx := b5_group Λ F hF Q hQ
  have gy := b5_group Μ G hG R hR
  have hmon : IsMonHom a := by
    apply (faithful_group_reflection_aux (b5_model Λ F hF Q) (b5_model Μ G hG R)).2
    · rw [← gx.1]
      change Point.map a (e 0) = 1
      rw [heq, map_zero]
      exact gy.1
    · intro x y
      obtain ⟨t, rfl⟩ := e.surjective x
      obtain ⟨u, rfl⟩ := e.surjective y
      change Point.map a (b5_theta Λ F hF Q hQ t * b5_theta Λ F hF Q hQ u) = _
      rw [← gx.2.1]
      change Point.map a (e (t + u)) = Point.map a (e t) * Point.map a (e u)
      rw [heq (t + u), heq t, heq u, map_add]
      exact gy.2.1 _ _
  refine ⟨a, ⟨hmon, heq⟩, ?_⟩
  intro b hb
  apply b55_hom_ext
  funext p
  obtain ⟨t, rfl⟩ := e.surjective p
  exact (hb.2 t).trans (heq t).symm

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


set_option maxHeartbeats 1000 in
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] :
    IsMonHom ((𝟙 X) * (𝟙 X)) := by
  rw [Hom.mul_def]
  infer_instance

end HodgeLean.Foundations.AnalyticAlbanese
