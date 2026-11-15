import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedInvariantCharts
import HodgeLean.Foundations.Program.SchoenTowerL1aLiftedAction
import HodgeLean.Foundations.Program.SchoenTowerL1aSchemeOpenRefinement

/-! # Prescribed neighborhoods for the retained symmetric quotient

Implication from the retained categorical quotient and a prescribed ordered
orbit neighborhood to a compatible affine target restriction.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained quotient has an affine target neighborhood whose actual
preimage lies in any prescribed neighborhood of the ordered point's orbit.
Source: Stacks Project, tag 04A9; Hartshorne, Algebraic Geometry, II.2–3. -/
theorem s2v_l1a_retained_affine_refinement
    (Z B : Over (Spec ↧ℂ)) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (x : ComplexPoint (g3_power Z (h + 1)))
    (W : (g3_power Z (h + 1)).left.Opens)
    (hW : ∀ τ, (Point.map (s2_permute Z (h + 1) τ) x).underlying ∈ W) :
    ∃ U : B.left.affineOpens,
      x.underlying ∈ γ.left ⁻¹ᵁ U.1 ∧ γ.left ⁻¹ᵁ U.1 ≤ W := by
  let X := g3_power Z (h + 1)
  obtain ⟨U, hx, hV, hq, ρ, hρ, hρq⟩ := s2v_l1a_invariant_affine_neighborhood
    γ.left (fun τ => (s2_permute Z (h + 1) τ).left)
    (fun τ => congrArg (fun f : X ⟶ B => f.left) (hγinv τ)) x.underlying
  let V := γ.left ⁻¹ᵁ U.1
  let Uo := ComplexPoint.openScheme B U.1
  let Vo := ComplexPoint.openScheme X V
  let u : Uo ⟶ B := ComplexPoint.openInclusion B U.1
  let v : Vo ⟶ X := ComplexPoint.openInclusion X V
  let q : Vo ⟶ Uo := Over.homMk (γ.left ∣_ U.1) (by
    change (γ.left ∣_ U.1) ≫ (U.1.ι ≫ B.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  let ρo (τ : Equiv.Perm (Fin (h + 1))) : Vo ⟶ Vo := Over.homMk (ρ τ) (by
    change ρ τ ≫ (V.ι ≫ X.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, hρ τ, Category.assoc, Over.w])
  have hρv (τ : Equiv.Perm (Fin (h + 1))) :
      ρo τ ≫ v = v ≫ s2_permute Z (h + 1) τ := by
    apply Over.OverMorphism.ext
    exact hρ τ
  letI : IsAffine Uo.left := U.2
  letI : IsAffine Vo.left := hV
  letI : IsOpenImmersion u.left := inferInstanceAs (IsOpenImmersion U.1.ι)
  letI : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion V.ι)
  letI : Mono v := Over.mono_of_mono_left v
  let act := s2v_l1a_liftedAction (s2_symmetricPowerAction Z (h + 1)) v ρo hρv
  let p := ComplexPoint.asOpenPoint X V x hx
  have hp : Point.map v p = x := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X V x hx
  have hVo (τ : Equiv.Perm (Fin (h + 1))) :
      (Point.map (act τ).asIso.hom p).underlying ∈ v.left ⁻¹ᵁ W := by
    have H : Point.map v (Point.map (ρo τ) p) =
        Point.map (s2_permute Z (h + 1) τ) x := by
      change (p ≫ ρo τ) ≫ v = x ≫ s2_permute Z (h + 1) τ
      rw [Category.assoc, hρv, ← Category.assoc]
      exact congrArg (fun f => f ≫ s2_permute Z (h + 1) τ) hp
    change (Point.map v (Point.map (ρo τ) p)).underlying ∈ W
    rw [H]
    exact hW τ
  obtain ⟨hinj, himage⟩ := s2v_l1a_retained_affine_invariants Z B h γ hγinv hγ U
  have Hinv := s2v_l1a_restricted_lift_invariant_image γ.left
    (fun τ => (s2_permute Z (h + 1) τ).left)
    (fun τ => congrArg (fun f : X ⟶ B => f.left) (hγinv τ)) U.1 hinj himage ρ hρ
  obtain ⟨c, hc, hsub⟩ := s2v_l1a_scheme_open_refinement Vo Uo
    (Equiv.Perm (Fin (h + 1))) act q Hinv.2 p (v.left ⁻¹ᵁ W) hVo
  let O := Uo.left.basicOpen c
  have hO : IsAffineOpen O := (isAffineOpen_top Uo.left).basicOpen c
  refine ⟨⟨u.left ''ᵁ O, hO.image_of_isOpenImmersion u.left⟩, ?_, ?_⟩
  · have hpc : (Point.map q p).underlying ∈ O :=
      (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero c (Point.map q p)
        (show Point.map q p ∈ Point.overOpen ⊤ from trivial)).mpr hc
    have H : Point.map u (Point.map q p) = Point.map γ x := by
      change (p ≫ q) ≫ u = x ≫ γ
      have hsquare : q ≫ u = v ≫ γ := by
        apply Over.OverMorphism.ext
        exact morphismRestrict_ι γ.left U.1
      rw [Category.assoc, hsquare, ← Category.assoc]
      exact congrArg (fun f => f ≫ γ) hp
    exact ⟨(Point.map q p).underlying, hpc, congrArg Point.underlying H⟩
  · change γ.left ⁻¹ᵁ (U.1.ι ''ᵁ O) ≤ W
    rw [← image_morphismRestrict_preimage γ.left U.1 O]
    exact (V.ι.image_mono hsub).trans (V.ι.image_preimage_le W)

end HodgeLean.Foundations.Program
