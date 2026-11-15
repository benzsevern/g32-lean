import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelFibreImmersion
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelFibrePoints
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelSmooth
import HodgeLean.Foundations.Program.G32Native.PairedResidualFibreImageIso
import HodgeLean.Foundations.Program.G32Native.PairedResidualFibreFactor
import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemImmersion

/-! # The actual full-system immersion into its specified Abel fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r d : ℕ)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm (Module.finrank_fin_fun (n := 1) ℂ) q ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0)
    [FiniteDimensional ℂ W]
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ W = d + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
      Point.map ℓ = fun R => residualProjectiveSystemPoint
        (Module.finrank_fin_fun (n := 1) ℂ) y hy W (fun q => (hW q.val).mp q.property) hgenus γ id (ep.symm R))
include hy hW hgenus hd hγ hsurj hquot hℓ
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The original full projective linear system is its actual smooth Abel
fibre, with the supplied immersion and both projections retained.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.6. -/
theorem residual_system_abel_fibre_iso
    (hr : 0 < r) (p : ComplexPoint Z)
    (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u)))
    (v : W) (hv : v ≠ 0) :
    let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
    let q₀ := ep (Projectivization.mk ℂ v hv)
    let z := Point.map (ℓ ≫ a) q₀
    ∃ e : (Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))).left ≅
        pullback a.left z.left,
      e.hom ≫ pullback.fst a.left z.left = ℓ.left ∧
      e.hom ≫ pullback.snd a.left z.left =
        ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ) := by
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
  let q₀ := ep (Projectivization.mk ℂ v hv)
  let z := Point.map (ℓ ≫ a) q₀
  change ∃ e : _ ≅ pullback a.left z.left, _
  letI : Surjective γ.left := s2e_step1_surjective_of_complexPoint_surjective _ _ γ hsurj
  letI : SmoothOfRelativeDimension (2 * k) B.hom :=
    s2e_retained_quotient_relative_dimension Z B (2 * k) γ hγ hquot
  have hsum : ∀ u, (theta (C := ComplexPoint Z) hOne).symm (Point.map a (Point.map γ u)) =
      ∑ i, analyticAbel hOne p (Point.map (g3_proj Z (2 * k) i) u) := by
    intro u
    have hu := (Point.map_comp_apply γ a u).symm.trans (congrFun ha u)
    exact (congrArg (theta (C := ComplexPoint Z) hOne).symm hu).trans
      ((theta (C := ComplexPoint Z) hOne).symm_apply_apply _)
  have hdeg : 2 * (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 <
      ((2 * k : ℕ) : ℤ) := by omega
  letI : Smooth a.left := residual_algebraic_abel_smooth Z B (2 * k) γ hγ hsurj hquot
    a p hsum hdeg
  obtain ⟨l, hl, hl₁, hl₂⟩ := residual_system_abel_fibre_immersion Z B k r d y hy W
    (fun q => (hW q.val).mp q.property) hgenus hd γ hγ hsurj hquot ℓ hℓ p a ha q₀
  letI : IsClosedImmersion l := hl
  letI : IsClosedImmersion z.left := by
    haveI : IsClosedImmersion (z.left ≫ (model (C := ComplexPoint Z) hOne).hom) := by
      rw [Over.w z]
      change IsClosedImmersion (𝟙 (Spec ↧ℂ))
      infer_instance
    exact IsClosedImmersion.of_comp z.left (model (C := ComplexPoint Z) hOne).hom
  have himage : ∀ q : ComplexPoint B, Point.map a q = z →
      ∃ t, Point.map ℓ t = q := by
    intro q hq
    have hq₀ : Point.map ℓ q₀ = residualProjectiveSystemPoint hOne y hy W
        (fun t => (hW t.val).mp t.property) hgenus γ id (Projectivization.mk ℂ v hv) := by
      rw [hℓ]
      exact congrArg _ (ep.symm_apply_apply _)
    have hvalue : Point.map a q = Point.map a (residualProjectiveSystemPoint hOne y hy W
        (fun t => (hW t.val).mp t.property) hgenus γ id (Projectivization.mk ℂ v hv)) :=
      hq.trans ((Point.map_comp_apply ℓ a q₀).trans (congrArg (Point.map a) hq₀))
    obtain ⟨t, ht⟩ := (residual_system_abel_fibre_points Z B k r y hy W hW hgenus p
      γ hsurj hγ a ha v hv q).mpr hvalue
    refine ⟨ep t, ?_⟩
    rw [hℓ]
    exact (congrArg _ (ep.symm_apply_apply t)).trans ht
  letI : IsIso l := residual_fibre_immersion_isIso_of_point_image _ B _ a z ℓ l hl₁ hl₂ himage
  exact ⟨asIso l, hl₁, hl₂⟩

#print axioms residual_system_abel_fibre_iso
end HodgeLean.Foundations.Program.G32Native
