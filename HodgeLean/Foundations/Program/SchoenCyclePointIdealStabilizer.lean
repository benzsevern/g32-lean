import HodgeLean.Foundations.Program.SchoenCycleStep1PointEvaluation
import Mathlib.RingTheory.Ideal.Maximal

/-! # Complex point ideals and their actual scheme stabilizers -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Complex-valued algebra evaluations with the same kernel coincide.
Source: Hartshorne, Algebraic Geometry, II.2, rational points and evaluation ideals. -/
theorem s2e_complex_evaluation_eq_of_ker_eq
    (A : Type*) [CommRing A] [Algebra ℂ A] (φ ψ : A →ₐ[ℂ] ℂ)
    (hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom) : φ = ψ := by
  ext r
  have hr : r - algebraMap ℂ A (φ r) ∈ RingHom.ker φ.toRingHom := by
    rw [RingHom.mem_ker]
    change φ (r - algebraMap ℂ A (φ r)) = 0
    rw [map_sub, φ.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [hker, RingHom.mem_ker] at hr
  change ψ (r - algebraMap ℂ A (φ r)) = 0 at hr
  rw [map_sub, ψ.commutes, Algebra.algebraMap_self, RingHom.id_apply] at hr
  exact (sub_eq_zero.mp hr).symm

/-- Equal complex points induce equal evaluation maps on a common affine chart.
Source: Hartshorne, Algebraic Geometry, II.2, evaluation of regular functions. -/
theorem s2e_pointEvaluation_congr
    (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (x y : ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ W) (hy : ⊤ ≤ y.left ⁻¹ᵁ W) (h : x = y) :
    s2e_step1_pointEvaluation X W x hx = s2e_step1_pointEvaluation X W y hy := by
  subst y
  rfl

/-- The stabilizer of the evaluation ideal on an actual affine chart is the
stabilizer of its actual complex point, with the pullback inverse made explicit.
Source: Hartshorne, Algebraic Geometry, II.2, rational points and evaluation ideals;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1. -/
theorem s2e_quotient_point_ideal_stabilizer
    (X Y : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q)
    (U : Y.left.Opens) (hW : IsAffineOpen (q.left ⁻¹ᵁ U))
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ (q.left ⁻¹ᵁ U)) (g : G) :
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, q.left ⁻¹ᵁ U)
    let ε := s2e_step1_pointEvaluation X (q.left ⁻¹ᵁ U) x hx
    (RingHom.ker ε.toRingHom).comap (α g).toRingHom = RingHom.ker ε.toRingHom ↔
      Point.map (a g⁻¹) x = x := by
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)
  let ε := s2e_step1_pointEvaluation X W x hx
  have hpre (u : G) : ⊤ ≤ (Point.map (a u) x).left ⁻¹ᵁ W := by
    intro z _
    change (a u).left (x.left z) ∈ W
    exact (s2e_step1_action_preimage X Y q (a u) (hinv u) U) (hx trivial)
  let xg := Point.map (a g⁻¹) x
  have hxg : ⊤ ≤ xg.left ⁻¹ᵁ W := hpre g⁻¹
  let εg := s2e_step1_pointEvaluation X W xg hxg
  have heval : εg = ε.comp (α g).toAlgHom := by
    ext r
    exact s2e_step1_pointEvaluation_map X W (a g⁻¹)
      (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U) x hx hxg r
  change RingHom.ker (ε.comp (α g).toAlgHom).toRingHom = RingHom.ker ε.toRingHom ↔ xg = x
  constructor
  · intro hk
    have he := s2e_complex_evaluation_eq_of_ker_eq Γ(X.left, W)
      (ε.comp (α g).toAlgHom) ε hk
    exact s2e_step1_point_ext_on_affine X W hW xg x hxg hx (heval.trans he)
  · intro hxx
    have he : εg = ε := by
      exact s2e_pointEvaluation_congr X W xg x hxg hx hxx
    exact congrArg (fun f : Γ(X.left, W) →ₐ[ℂ] ℂ => RingHom.ker f.toRingHom)
      (heval.symm.trans he)

/-- Affine evaluation at an actual complex point is evaluation of the germ by
the actual point stalk map.
Source: Mathlib, AlgebraicGeometry.Scheme.germ_stalkClosedPointTo;
Hartshorne, Algebraic Geometry, II.2, evaluation of regular functions. -/
theorem s2e_pointEvaluation_stalk_factor
    (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (x : ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ W) :
    letI := s2e_step1_sectionAlgebra X W
    (s2e_step1_pointEvaluation X W x hx).toRingHom =
      x.stalkHom.hom.comp (X.left.presheaf.germ W x.underlying (hx trivial)).hom := by
  letI := s2e_step1_sectionAlgebra X W
  let f : Spec (CommRingCat.of ℂ) ⟶ X.left := x.left
  have hc : X.left.presheaf.germ W x.underlying (hx trivial) ≫ x.stalkHom =
      x.left.appLE W ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    change X.left.presheaf.germ W (f (IsLocalRing.closedPoint ℂ)) _ ≫
      Scheme.stalkClosedPointTo f = f.appLE W ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    rw [Scheme.germ_stalkClosedPointTo (f := f)]
    dsimp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    simp only [Category.assoc]
    congr 2
  exact (congrArg CommRingCat.Hom.hom hc).symm

/-- The actual complex evaluation ideal is the affine prime ideal of the actual
underlying scheme point.
Source: Hartshorne, Algebraic Geometry, II.2, rational points and evaluation ideals;
Mathlib, AlgebraicGeometry.IsAffineOpen.primeIdealOf_eq_map_closedPoint. -/
theorem s2e_pointEvaluation_kernel_primeIdealOf
    (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (hW : IsAffineOpen W)
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ W) :
    letI := s2e_step1_sectionAlgebra X W
    RingHom.ker (s2e_step1_pointEvaluation X W x hx).toRingHom =
      (hW.primeIdealOf ⟨x.underlying, hx trivial⟩).asIdeal := by
  letI := s2e_step1_sectionAlgebra X W
  have hk : RingHom.ker x.stalkHom.hom = IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) := by
    change (⊥ : Ideal ℂ).comap x.stalkHom.hom = _
    rw [← IsLocalRing.maximalIdeal_eq_bot (R := ℂ), IsLocalRing.maximalIdeal_comap]
  rw [s2e_pointEvaluation_stalk_factor]
  change (RingHom.ker x.stalkHom.hom).comap
    (X.left.presheaf.germ W x.underlying (hx trivial)).hom = _
  rw [hk, hW.primeIdealOf_eq_map_closedPoint]
  rfl

/-- Fixing an actual complex point fixes its underlying scheme point.
Source: Hartshorne, Algebraic Geometry, II.2, points as morphisms from spectra. -/
theorem s2e_complex_point_fixed_underlying (X : Over (Spec ↧ℂ))
    (f : X ⟶ X) (x : ComplexPoint X) (h : Point.map f x = x) :
    f.left x.underlying = x.underlying := by
  change (Point.map f x).underlying = x.underlying
  exact congrArg Point.underlying h

end HodgeLean.Foundations.Program
