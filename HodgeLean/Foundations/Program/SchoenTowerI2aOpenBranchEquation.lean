import HodgeLean.Foundations.Program.SchoenTowerI2aOpenCoefficientSquare
import HodgeLean.Foundations.Program.SchoenTowerI2aBranchCoefficientTransport
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldOpenFactor
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! A restricted section equation on the actual affine open scheme.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A weighted equation on affine-open sections gives an equation on the actual open scheme, retaining the complex point and original-field factor. -/
theorem s2v_i2a_open_scheme_branch_equation
    {K : Type} [Field K] (X : Over (Spec ↧ℂ))
    (p : ComplexPoint X) (η : Spec (.of K) ⟶ X.left) [IsDominant η]
    (O : X.left.affineOpens) (hp : p.underlying ∈ O.1)
    (hO : ⊤ ≤ η ⁻¹ᵁ O.1)
    {T : Type} [Fintype T] (z : T → Γ(X.left, ⊤)) (n : T → ℕ)
    (v : K) (m : ℕ) (ε : Γ(X.left, O)ˣ)
    (hv : v ^ m = (η.appLE O.1 ⊤ hO ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ε *
      ∏ t, (η.appLE O.1 ⊤ hO ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
        (X.left.presheaf.map (homOfLE (show O.1 ≤ ⊤ from le_top)).op (z t)) ^ n t)
    (hgen : Subfield.closure
      (Set.range (η.appLE O.1 ⊤ hO ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {v}) = ⊤) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (k : V ⟶ X)
      (ηV : Spec (.of K) ⟶ V.left) (εV : Γ(V.left, ⊤)),
      IsOpenImmersion k.left ∧ p ∈ Set.range (Point.map k) ∧
      ηV ≫ k.left = η ∧ IsUnit εV ∧
      let φ := (ηV.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
      v ^ m = φ εV * ∏ t, φ (k.left.appTop.hom (z t)) ^ n t ∧
      Subfield.closure (Set.range φ ∪ {v}) = ⊤ := by
  let V := ComplexPoint.openScheme X O.1
  let k : V ⟶ X := ComplexPoint.openInclusion X O.1
  let q : ComplexPoint V := ComplexPoint.asOpenPoint X O.1 p hp
  letI : IsAffine V.left := O.2
  letI : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion O.1.ι)
  letI : Nonempty V.left := ⟨q.underlying⟩
  obtain ⟨ηV, hηV, _⟩ := s2v_i2a_dominant_field_point_open_factor k.left η
  let ψ : Γ(X.left, O) ⟶ Γ(V.left, ⊤) := O.1.ι.appLE O.1 ⊤ O.1.ι_preimage_self.ge
  let ρ := (η.appLE O.1 ⊤ hO ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
  let φ := (ηV.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
  let res := (X.left.presheaf.map (homOfLE (show O.1 ≤ ⊤ from le_top)).op).hom
  have hcomp : φ.comp ψ.hom = ρ :=
    s2v_i2a_open_coefficient_square X.left O.1 η ηV hηV.1 hO
  have hres : ψ.hom.comp res = k.left.appTop.hom := by
    change (X.left.presheaf.map (homOfLE (show O.1 ≤ ⊤ from le_top)).op ≫ ψ).hom = _
    dsimp only [ψ]
    rw [Scheme.Hom.map_appLE]
    have ht : O.1.ι.appLE ⊤ ⊤ (by simp) = O.1.ι.appTop := by
      simpa only [TopologicalSpace.Opens.map_top] using
        (Scheme.Hom.appLE_eq_app O.1.ι (U := ⊤))
    exact congrArg CommRingCat.Hom.hom ht
  have hpoint (a : Γ(X.left, O)) : φ (ψ a) = ρ a := DFunLike.congr_fun hcomp a
  have hz (t : T) : ψ (res (z t)) = k.left.appTop.hom (z t) :=
    DFunLike.congr_fun hres (z t)
  let εV : Γ(V.left, ⊤)ˣ := Units.map ψ.hom.toMonoidHom ε
  refine ⟨V, inferInstance, k, ηV, εV, inferInstance, ⟨q, ?_⟩, hηV.1, εV.isUnit, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X O.1 p hp
  · change v ^ m = φ (ψ (ε : Γ(X.left, O))) * ∏ t, φ (k.left.appTop.hom (z t)) ^ n t
    rw [hpoint]
    simpa only [← hz, hpoint] using hv
  · exact s2v_i2a_generator_under_coefficient_map ψ.hom ρ φ hcomp v hgen

end HodgeLean.Foundations.Program
