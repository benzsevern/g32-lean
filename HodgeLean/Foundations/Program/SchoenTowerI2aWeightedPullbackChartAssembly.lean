import HodgeLean.Foundations.Program.SchoenTowerI2aWeightedPullbackEquation
import HodgeLean.Foundations.Program.SchoenTowerI2aStalkChartAssembly

/-! Affine refinement from original-base equations and actual weighted transforms.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A weighted ideal transform and original-base rational equation yield the supplied strict branch chart after affine refinement. -/
theorem s2v_i2a_weighted_pullback_chart_assembly
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
    {Y : Scheme.{0}} [IsIntegral Y] (f : U.left ⟶ Y)
    (κY : Y.functionField ⟶ CommRingCat.of K)
    (hsq : Spec.map κF ≫ U.left.fromSpecStalk (genericPoint U.left) ≫ f =
      Spec.map κY ≫ Y.fromSpecStalk (genericPoint Y))
    (I : T → Y.IdealSheafData) (E : U.left.IdealSheafData) (m : ℕ)
    (htransform : (∏ t, (I t) ^ n t).comap f = (∏ t, (D t) ^ n t) * E ^ m)
    (O : Y.affineOpens) (hpO : f p.underlying ∈ O.1)
    (g : T → Γ(Y, O)) (hg : ∀ t, (I t).ideal O = Ideal.span {g t})
    (e : U.left.presheaf.stalk p.underlying) (he_ne : e ≠ 0)
    (he : (E.ideal ⟨⊤, isAffineOpen_top _⟩).map
      (U.left.presheaf.germ ⊤ p.underlying (by trivial)).hom = Ideal.span {e})
    (ε : (Y.presheaf.stalk (f p.underlying))ˣ)
    (A B : Y.presheaf.stalk (f p.underlying)) (hA : A ≠ 0) (hB : B ≠ 0)
    (v : K)
    (hgen : Subfield.closure (Set.range (s2v_l1b_kval_stalkMap U.left p.underlying κF) ∪ {v}) = ⊤)
    (hv : let ρ := s2v_l1b_kval_stalkMap Y (f p.underlying) κY
      v ^ m * (ρ B) ^ m = ρ (ε : Y.presheaf.stalk (f p.underlying)) *
        (∏ t, ρ ((Y.presheaf.germ O.1 (f p.underlying) hpO).hom (g t)) ^ n t) *
          (ρ A) ^ m) :
    ∃ w : K, ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (k : V ⟶ U)
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
      w ^ m = φ εV * ∏ t, φ (zV t) ^ n t ∧ Subfield.closure (Set.range φ ∪ {w}) = ⊤ := by
  obtain ⟨w, δ, hwgen, hweq⟩ := s2v_i2a_weighted_pullback_equation f κF κY hsq
    p.underlying I D E n m htransform ⟨⊤, isAffineOpen_top _⟩ O (by trivial) hpO
    g z hg hideal e he_ne he ε A B hA hB v hv hgen
  refine ⟨w, ?_⟩
  exact s2v_i2a_stalk_branch_chart_assembly U p η κF hη D z n hideal N c hc
    hscalar J κ hz habsent w m δ hwgen hweq

end HodgeLean.Foundations.Program
