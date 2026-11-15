import HodgeLean.Foundations.Program.SchoenCycleRetainedStabilizerMarkedEtaleMorphism
import HodgeLean.Foundations.Program.SchoenCycleMixedStabilizerCenteredEtaleSections
import HodgeLean.Foundations.Program.SchoenCycleEtaleOpenCoefficientDescent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The exact mixed stabilizer sections give a centered analytic chart on the original retained quotient, with analytic inverse and their exact evaluations on the actual marked stabilizer comparison neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_mixed_stabilizer_exact_analytic_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (U : B.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint (g3_power Z n)) (hxU : x.underlying ∈ γ.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set (g3_power Z n).left))
    [SmoothOfRelativeDimension n B.hom]
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a) :
    letI := s2e_step1_sectionAlgebra B U
    let H := s2e_powerPointStabilizer Z n x
    letI : Fintype H := Fintype.ofFinite H
    let a := fun σ : H => s2_permute Z n σ.val
    let ha1 : a 1 = 𝟙 (g3_power Z n) := s2e_step1_permute_one Z n
    let hamul : ∀ u v, a (u * v) = a v ≫ a u := fun u v => s2e_step1_permute_mul Z n u.val v.val
    let hinv := fun σ : H => hγ σ.val
    let hfix := fun σ : H => s2e_complex_point_fixed_underlying (g3_power Z n)
      (a σ) x σ.property
    let W := γ.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra (g3_power Z n) W
    letI := s2e_step1_sectionAction (g3_power Z n) B H a ha1 hamul γ hinv U
    letI := s2e_step1_sectionAction_smulComm (g3_power Z n) B H a ha1 hamul γ hinv U
    let P := ((hU.preimage γ.left).primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
    let S := FixedPoints.subalgebra ℂ Γ((g3_power Z n).left, W) H
    let Q := P.under S
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    let XS := Over.mk (ComplexPoint.affineSpecStructureMap S)
    let T (g : S) := Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g))
    let loc (g : S) : ComplexPoint (T g) → ComplexPoint XS :=
      ComplexPoint.affineSpecComplexPointMap (IsScalarTower.toAlgHom ℂ S (Localization.Away g))
    ∃ (z : ComplexPoint XS), z.underlying.asIdeal = Q ∧
      ∃ F₀ : XS.left.presheaf.stalk z.underlying →+* R,
        (∀ s : S, F₀ ((XS.left.presheaf.germ ⊤ z.underlying trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) =
            ((g3_power Z n).left.presheaf.germ (γ.left ⁻¹ᵁ U) x.underlying hxU).hom s.val) ∧
        ∃ (V : XS.left.Opens) (_ : IsAffineOpen V) (hzV : z.underlying ∈ V),
          ∃ G : MvPolynomial (Fin n) ℂ →+* Γ(XS.left, V),
            G.Etale ∧
            (∀ a (j : Fin (m a)), F₀ ((XS.left.presheaf.germ V z.underlying hzV).hom
              (G (MvPolynomial.X (ι ⟨a, j⟩)))) =
                aeval (s2e_curvePowerParameter Z n x)
                  (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m (MvPolynomial.X ⟨a, j⟩)).val)) ∧
            ∃ g : S, g ∉ Q ∧
              ∃ (w : ComplexPoint (T g))
                (f : T g ⟶ B),
                ∃ Fbase : Γ(B.left, U) →ₐ[ℂ] S,
                (∀ a, (Fbase a).val = (γ.left.app U).hom a) ∧
                Etale f.left ∧
                loc g w = z ∧
                Point.map f w = Point.map γ x ∧
                (∀ (q : ComplexPoint (T g)) (a : Γ(B.left, U)),
                  Point.evaluate U a (Point.map f q) =
                    ComplexPoint.affineSpecEquiv (Localization.Away g) q
                      (algebraMap S (Localization.Away g) (Fbase a))) ∧
                ∃ e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ),
                  Point.map γ x ∈ e.source ∧ e (Point.map γ x) = 0 ∧
                  AnalyticAt ℂ (fun v => e ((ComplexPoint.localChart B n (Point.map γ x)).symm
                    (ComplexPoint.localChart B n (Point.map γ x) (Point.map γ x) + v))) 0 ∧
                  AnalyticAt ℂ (fun v => ComplexPoint.localChart B n (Point.map γ x) (e.symm v)) 0 ∧
                  (∀ᶠ q in 𝓝 w, ∀ i, e (Point.map f q) i =
                    Point.evaluate V (G (MvPolynomial.X i))
                      (loc g q)) := by
  let A := Γ(B.left, U)
  let C := Γ((g3_power Z n).left, γ.left ⁻¹ᵁ U)
  let G := Equiv.Perm (Fin n)
  letI := s2e_step1_sectionAlgebra B U
  letI := s2e_step1_sectionAlgebra (g3_power Z n) (γ.left ⁻¹ᵁ U)
  letI : Algebra A C := (γ.left.app U).hom.toAlgebra
  letI := s2e_complex_section_app_tower (g3_power Z n) B γ U
  letI := s2e_step1_sectionAction (g3_power Z n) B G
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  letI := s2e_quotient_sectionAction_base_smulComm (g3_power Z n) B G
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  letI := s2e_step1_sectionAction_smulComm (g3_power Z n) B G
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  let H := s2e_powerPointStabilizer Z n x
  let S := FixedPoints.subalgebra ℂ C H
  letI : Algebra A S := (s2e_fixed_action_base_map ℂ A C H).toAlgebra
  letI : IsScalarTower ℂ A S := (s2e_fixed_function_scalar_towers ℂ A C H).1
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let XS := Over.mk (ComplexPoint.affineSpecStructureMap S)
  obtain ⟨z, hz, F₀, hF₀, V, hV, hzV, G₀, hG₀, hzero, hval⟩ :=
    s2e_mixed_stabilizer_centered_etale_sections Z B n γ hγ U (hU.preimage γ.left)
      x hxU b m ι p hp hx hcx
  letI := s2e_step1_sectionAlgebra XS V
  obtain ⟨g, hg, w, f, hf, hw, hfx, hv⟩ :=
    s2e_retained_stabilizer_marked_etale_morphism Z B n γ hγ hquot U hU x hxU hcx z hz
  let T := Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g))
  let L : S →ₐ[ℂ] Localization.Away g := IsScalarTower.toAlgHom ℂ S (Localization.Away g)
  let a : T ⟶ XS := Over.homMk (Spec.map (CommRingCat.ofHom L.toRingHom))
    (ComplexPoint.specMap_comp_affineSpecStructureMap L)
  have ha : Etale a.left := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale S (Localization.Away g))
  have haw : Point.map a w = z := hw
  obtain ⟨e, he, hez, hef, hei, hev⟩ :=
    s2e_etale_open_coefficient_chart_descent XS B T n V hV G₀ hG₀ a f ha hf w
      (by rw [haw]; exact hzV) (fun i => by rw [haw]; exact hzero i)
  refine ⟨z, hz, F₀, hF₀, V, hV, hzV, G₀.toRingHom, hG₀, hval, g, hg, w, f, s2e_fixed_action_base_map ℂ A C H, (fun a => rfl), hf, hw, hfx, hv,
    e, ?_, ?_, ?_, ?_, hev⟩
  · rwa [hfx] at he
  · rwa [hfx] at hez
  · rwa [hfx] at hef
  · rwa [hfx] at hei

#print axioms s2e_mixed_stabilizer_exact_analytic_descent
end HodgeLean.Foundations.Program
