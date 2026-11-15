import HodgeLean.Foundations.Program.SchoenTowerConormalDefs

/-! # Data of a retained residual-component presentation -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A scheme-theoretic residual-component presentation. The objects and
maps are retained, rather than just an exactness assertion. The two endpoint
identifications record the fibre normal and the residual hyperplane normal.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7, pp. 16–17;
Fulton, Intersection Theory, §6.7, strict transforms. -/
structure PairedResidualPresentation
    (P V : Over (Spec ↧ℂ)) (t₁ : P ⟶ V) (k : ℕ) (L : P.left.Modules) where
  T : Over (Spec ↧ℂ)
  T₂ : Over (Spec ↧ℂ)
  S : Over (Spec ↧ℂ)
  t : T ⟶ V
  t₂ : T₂ ⟶ V
  a : P ⟶ T
  s₁ : S ⟶ P
  s₂ : S ⟶ T₂
  closed_t : IsClosedImmersion t.left
  closed_t₂ : IsClosedImmersion t₂.left
  closed_a : IsClosedImmersion a.left
  closed_s₁ : IsClosedImmersion s₁.left
  closed_s₂ : IsClosedImmersion s₂.left
  smooth_T₂ : Smooth T₂.hom
  ha : a ≫ t = t₁
  hs : s₁ ≫ t₁ = s₂ ≫ t₂
  union_ideal : t.left.ker = t₁.left.ker ⊓ t₂.left.ker
  intersection_ideal : (s₁ ≫ t₁).left.ker = t₁.left.ker ⊔ t₂.left.ker
  noncontainment : ¬ Set.range t₁.left ⊆ Set.range t₂.left
  sourceIso : (Scheme.Modules.pullback a.left).obj (s2c_conormal t.left) ≅
    (SheafOfModules.free (R := P.left.ringCatSheaf) (Fin k) : P.left.Modules)
  lastIso : (Scheme.Modules.pushforward s₁.left).obj (s2c_conormal s₂.left) ≅ L
  local_frames : ∀ x : P.left, ∃ U : P.left.Opens, x ∈ U ∧
    Nonempty (Scheme.Modules.restrict
      ((Scheme.Modules.pullback a.left).obj (s2c_conormal t.left)) U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) ∧
    Nonempty (Scheme.Modules.restrict (s2c_conormal t₁.left) U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))

end HodgeLean.Foundations.Program.G32Native
