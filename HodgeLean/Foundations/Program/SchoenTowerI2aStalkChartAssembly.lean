import HodgeLean.Foundations.Program.SchoenTowerI2aOpenBranchEquation
import HodgeLean.Foundations.Program.SchoenTowerI2aStalkBranchRefinement
import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedPointIdeals

/-! Actual affine chart assembly from a weighted stalk equation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A weighted equation in the actual stalk yields an affine chart refinement with all supplied polynomial coordinates, labels and branch equations retained. -/
theorem s2v_i2a_stalk_branch_chart_assembly
    {K : Type} [Field K] (U : Over (Spec ↧ℂ)) [IsAffine U.left] [IsIntegral U.left]
    (p : ComplexPoint U) (η : Spec (.of K) ⟶ U.left) [IsDominant η]
    (κF : U.left.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κF ≫ U.left.fromSpecStalk (genericPoint U.left) = η)
    {T : Type} [Fintype T] (D : T → U.left.IdealSheafData)
    (z : T → Γ(U.left, ⊤)) (n : T → ℕ)
    (hideal : ∀ t, (D t).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {z t})
    (N : ℕ) (c : MvPolynomial (Fin N) ℂ →+* Γ(U.left, ⊤)) (hc : c.Etale)
    (hscalar : c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    (J : Finset T) (κ : J ↪ Fin N)
    (hz : ∀ t : J, z t = c (MvPolynomial.X (κ t)))
    (habsent : ∀ t, t ∉ J → z t = 1)
    (v : K) (m : ℕ) (ε : (U.left.presheaf.stalk p.underlying)ˣ)
    (hgen : Subfield.closure (Set.range (s2v_l1b_kval_stalkMap U.left p.underlying κF) ∪ {v}) = ⊤)
    (hv : v ^ m = s2v_l1b_kval_stalkMap U.left p.underlying κF ε *
      ∏ t, s2v_l1b_kval_stalkMap U.left p.underlying κF
        (U.left.presheaf.germ ⊤ p.underlying (by trivial) (z t)) ^ n t) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (k : V ⟶ U)
      (ηV : Spec (.of K) ⟶ V.left)
      (cV : MvPolynomial (Fin N) ℂ →+* Γ(V.left, ⊤))
      (zV : T → Γ(V.left, ⊤)) (εV : Γ(V.left, ⊤)),
      IsOpenImmersion k.left ∧ p ∈ Set.range (Point.map k) ∧ ηV ≫ k.left = η ∧
      cV = k.left.appTop.hom.comp c ∧ (∀ t, zV t = k.left.appTop.hom (z t)) ∧
      cV.Etale ∧ cV.comp MvPolynomial.C =
        ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
      (∀ t : J, zV t = cV (MvPolynomial.X (κ t))) ∧
      (∀ t, t ∉ J → zV t = 1) ∧
      (∀ t, ((D t).comap k.left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {zV t}) ∧
      IsUnit εV ∧
      let φ := (ηV.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
      v ^ m = φ εV * ∏ t, φ (zV t) ^ n t ∧ Subfield.closure (Set.range φ ∪ {v}) = ⊤ := by
  obtain ⟨O, hηO, εO, hpO, hEtO, hDO, hpowO, hgenO⟩ :=
    s2v_i2a_stalk_branch_refinement U.left p.underlying η κF hη D z n hideal c hc v m ε hgen hv
  obtain ⟨V, hV, k, ηV, εV, hk, hpV, hηV, hunit, hpow, hfield⟩ :=
    s2v_i2a_open_scheme_branch_equation U p η O hpO hηO z n v m εO hpowO hgenO
  letI : IsAffine V.left := hV
  letI : IsOpenImmersion k.left := hk
  let cV := k.left.appTop.hom.comp c
  let zV : T → Γ(V.left, ⊤) := fun t => k.left.appTop.hom (z t)
  refine ⟨V, hV, k, ηV, cV, zV, εV, hk, hpV, hηV, rfl, (fun _ => rfl), ?_, ?_, ?_, ?_, ?_, hunit, hpow, hfield⟩
  · exact RingHom.Etale.stableUnderComposition _ _ hc
      (HasRingHomProperty.appTop (P := @Etale) k.left inferInstance)
  · change (k.left.appTop.hom.comp c).comp MvPolynomial.C = _
    rw [RingHom.comp_assoc, hscalar]
    change ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop ≫ k.left.appTop).hom = _
    rw [← Scheme.Hom.comp_appTop, k.w]
  · intro t
    exact congrArg k.left.appTop.hom (hz t)
  · intro t ht
    change k.left.appTop.hom (z t) = 1
    rw [habsent t ht, map_one]
  · intro t
    rw [s2v_l1a_affine_ideal_pullback, hideal t, Ideal.map_span, Set.image_singleton]

end HodgeLean.Foundations.Program
