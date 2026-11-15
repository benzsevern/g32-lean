import HodgeLean.Foundations.Program.TorusAlgebraizationB54LocalCarrier

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Point Set
namespace HodgeLean.Foundations.Program

theorem b54_evaluate_openImmersion {X Y : Over (Spec ↧ℂ)} (f : Y ⟶ X)
    [IsOpenImmersion f.left] (V : Y.left.Opens) (t : Γ(Y.left, V))
    (z : ComplexPoint Y) :
    evaluate (f.left ''ᵁ V) ((f.left.appIso V).inv t) (map f z) = evaluate V t z := by
  rw [evaluate_map]
  let e : f.left ⁻¹ᵁ f.left ''ᵁ V = V := f.left.preimage_image_eq V
  let q := f.left.app (f.left ''ᵁ V) ((f.left.appIso V).inv t)
  have hq : q = Y.left.presheaf.map (eqToHom e).op t := by
    change ((f.left.appIso V).inv ≫ f.left.app (f.left ''ᵁ V)) t = _
    rw [f.left.appIso_inv_app]
  calc
    evaluate (f.left ⁻¹ᵁ f.left ''ᵁ V) q z =
        evaluate V (Y.left.presheaf.map (eqToHom e.symm).op q) z :=
      evaluate_eq e q z
    _ = evaluate V t z := by
      congr 2
      rw [hq]
      change (Y.left.presheaf.map (eqToHom e).op ≫
        Y.left.presheaf.map (eqToHom e.symm).op) t = t
      rw [← Functor.map_comp]
      simp

theorem b54_point_lift_openImmersion {X Y : Over (Spec ↧ℂ)} (f : Y ⟶ X)
    [IsOpenImmersion f.left] (p : ComplexPoint X)
    (hp : p.underlying ∈ Set.range f.left) : ∃ q : ComplexPoint Y, map f q = p := by
  have hr : Set.range p.left ⊆ Set.range f.left := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
    subst x
    exact hp
  let g := IsOpenImmersion.lift f.left p.left hr
  have hg : g ≫ f.left = p.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
  rw [← f.w, ← Category.assoc, hg]
  exact p.w

theorem b54_mem_zeroLocus_iff_evaluate {X : Over (Spec ↧ℂ)} (U : X.left.Opens)
    (s : Set Γ(X.left, U)) (p : ComplexPoint X) (hp : p.underlying ∈ U) :
    p.underlying ∈ X.left.zeroLocus s ↔ ∀ t ∈ s, evaluate U t p = 0 := by
  rw [Scheme.mem_zeroLocus_iff]
  apply forall₂_congr
  intro t ht
  exact not_congr (mem_overOpen_basicOpen_iff_evaluate_ne_zero t p hp) |>.trans not_ne_iff

/-- Equations on open chart schemes determine a closed carrier on the ambient scheme.
Source: Hartshorne, Algebraic Geometry, II, Section 2. -/
theorem b54_closed_carrier_of_open_chart_equations (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X))
    (hlocal : ∀ p : ComplexPoint X, ∃ (Y : Over (Spec ↧ℂ)) (f : Y ⟶ X),
      IsOpenImmersion f.left ∧ p.underlying ∈ Set.range f.left ∧
      ∃ s : Set Γ(Y.left, ⊤), ∀ q : ComplexPoint Y,
        (map f q ∈ Z ↔ ∀ t ∈ s, evaluate ⊤ t q = 0)) :
    ∃ C : Set X.left, IsClosed C ∧ Z = Point.underlying ⁻¹' C := by
  apply b54_closed_carrier_of_local_equations X Z
  intro p
  obtain ⟨Y, f, hf, hp, s, hs⟩ := hlocal p
  letI := hf
  let U := f.left ''ᵁ ⊤
  have hU : (U : Set X.left) = Set.range f.left := by
    simp [U, Scheme.Hom.coe_image]
  refine ⟨U, (f.left.appIso ⊤).inv '' s, ?_, ?_⟩
  · change p.underlying ∈ (U : Set X.left)
    rwa [hU]
  · intro q hq
    obtain ⟨r, rfl⟩ := b54_point_lift_openImmersion f q (by rwa [← hU])
    rw [b54_mem_zeroLocus_iff_evaluate U _ _ hq, hs]
    simp only [Set.forall_mem_image]
    change (∀ t ∈ s, evaluate ⊤ t r = 0) ↔
      ∀ t ∈ s, evaluate (f.left ''ᵁ ⊤) ((f.left.appIso ⊤).inv t) (map f r) = 0
    simp only [b54_evaluate_openImmersion]

end HodgeLean.Foundations.Program
