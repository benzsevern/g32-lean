import HodgeLean.Foundations.Program.SchoenCycleMixedStabilizerExactAnalyticDescent
import HodgeLean.Foundations.Program.SchoenCycleLocalizedSubalgebraMorphism
import HodgeLean.Foundations.Program.SchoenCycleLocalizedSubalgebraBaseComparison
import HodgeLean.Foundations.Program.SchoenCycleAffineLocalizationPointInjective
import HodgeLean.Foundations.Program.SchoenCycleOpenAffineSectionPullback
import HodgeLean.Foundations.Program.SchoenCyclePowerPolynomialEvaluation
import HodgeLean.Foundations.Program.SchoenCycleOpenPointEventually

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original retained quotient has an analytic chart with analytic inverse whose exact upstairs values are the indexed elementary coefficients of the original centered native curve coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_mixed_elementary_analytic_neighbourhood
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    [SmoothOfRelativeDimension n B.hom]
    (x : ComplexPoint (g3_power Z n)) (b : ℕ) (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ),
      Point.map γ x ∈ e.source ∧ e (Point.map γ x) = 0 ∧
      AnalyticAt ℂ (fun v => e ((ComplexPoint.localChart B n (Point.map γ x)).symm
        (ComplexPoint.localChart B n (Point.map γ x) (Point.map γ x) + v))) 0 ∧
      AnalyticAt ℂ (fun v => ComplexPoint.localChart B n (Point.map γ x) (e.symm v)) 0 ∧
      (∀ᶠ q in 𝓝 x, ∀ a (j : Fin (m a)),
        e (Point.map γ q) (ι ⟨a, j⟩) = aeval (fun i : Fin (m a) =>
          ComplexPoint.localChart Z 1 (p a) (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) 0 -
            ComplexPoint.localChart Z 1 (p a) (p a) 0) (esymm (Fin (m a)) ℂ (j.val + 1))) := by
  let X := g3_power Z n
  obtain ⟨U, hU, hxU, hUT⟩ := exists_isAffineOpen_mem_and_subset
    (X := B.left) (x := γ.left x.underlying) (U := ⊤) trivial
  let W := γ.left ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage γ.left
  letI : IsClosedImmersion (x.left ≫ X.hom) := by
    rw [Over.w x]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left X.hom
  have hcx : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  let H := s2e_powerPointStabilizer Z n x
  letI : Fintype H := Fintype.ofFinite H
  let aH := fun σ : H => s2_permute Z n σ.val
  let ha1 : aH 1 = 𝟙 X := s2e_step1_permute_one Z n
  let hamul : ∀ u v, aH (u * v) = aH v ≫ aH u := fun u v => s2e_step1_permute_mul Z n u.val v.val
  let hinv := fun σ : H => hγ σ.val
  letI := s2e_step1_sectionAlgebra B U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X B H aH ha1 hamul γ hinv U
  letI := s2e_step1_sectionAction_smulComm X B H aH ha1 hamul γ hinv U
  let S := FixedPoints.subalgebra ℂ Γ(X.left, W) H
  let XS := Over.mk (ComplexPoint.affineSpecStructureMap S)
  let R := X.left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  obtain ⟨z, hz, F₀, hF₀, V, hV, hzV, G, hG, hval, g, hg, w, f, Fbase, hFbase,
    hf, hw, hfx, hfbase, e, he, hez, hef, hei, hev⟩ :=
    s2e_mixed_stabilizer_exact_analytic_descent Z B n γ hγ hquot U hU x hxU hcx b m ι p hp hx
  let P := (hW.primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
  letI : Algebra Γ(X.left, W) R := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨x.underlying, hxU⟩
  letI : IsLocalization.AtPrime R P := hW.isLocalization_stalk ⟨x.underlying, hxU⟩
  have hxg : x.underlying ∈ X.left.basicOpen g.val := by
    apply (X.left.mem_basicOpen g.val x.underlying hxU).mpr
    exact IsLocalization.map_units R (⟨g.val, hg⟩ : P.primeCompl)
  let Vg := X.left.basicOpen g.val
  let Y := ComplexPoint.openScheme X Vg
  let η := ComplexPoint.openInclusion X Vg
  let xY := (ComplexPoint.openHomeomorph X Vg).symm ⟨x, hxg⟩
  have hηx : Point.map η xY = x :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph X Vg).apply_symm_apply ⟨x, hxg⟩)
  have hηunder : xY.underlying.val = x.underlying := by
    have hh := congrArg Point.underlying hηx
    rw [Point.underlying_map] at hh
    change Vg.ι xY.underlying = x.underlying at hh
    exact hh
  obtain ⟨u, huglobal, hu⟩ := s2e_localized_subalgebra_morphism X W hW S g
  let T := Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g))
  let L : S →ₐ[ℂ] Localization.Away g := IsScalarTower.toAlgHom ℂ S (Localization.Away g)
  let a : T ⟶ XS := Over.homMk (Spec.map (CommRingCat.ofHom L.toRingHom))
    (ComplexPoint.specMap_comp_affineSpecStructureMap L)
  let fu := u ≫ a
  have huxz : Point.map a (Point.map u xY) = z := by
    apply (ComplexPoint.affineSpecEquiv S).injective
    ext s
    have hh := congrArg (fun F : S →ₐ[ℂ] ℂ => F s)
      (ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap L (Point.map u xY))
    calc
      ComplexPoint.affineSpecEquiv S (Point.map a (Point.map u xY)) s =
          ComplexPoint.affineSpecEquiv (Localization.Away g) (Point.map u xY) (algebraMap S (Localization.Away g) s) := hh
      _ = Point.evaluate W s.val x := by rw [hu xY s, hηx]
      _ = ComplexPoint.affineSpecEquiv S z s :=
        (s2e_identified_subalgebra_point_evaluation X W hW x
          (s2e_step1_point_preimage X x W hxU) S z hz s).symm
  have hux : Point.map u xY = w :=
    s2e_affine_localization_point_map_injective S g (huxz.trans hw.symm)
  have hfu : Point.map fu xY = z := by
    change xY ≫ (u ≫ a) = z
    rw [← Category.assoc]
    exact huxz
  have hfuunder : fu.left xY.underlying = z.underlying := by
    have hh := congrArg Point.underlying hfu
    simpa only [Point.underlying_map] using hh
  have hηW (q : ComplexPoint Y) : Point.map η q ∈ Point.overOpen W :=
    X.left.basicOpen_le g.val q.underlying.property
  have hbase := s2e_localized_subalgebra_base_comparison X B Y γ U hU η hηW S Fbase hFbase g u hu f hfbase
  have hglobal (s : S) : fu.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) =
      Vg.topIso.inv ((X.left.presheaf.map (homOfLE (X.left.basicOpen_le g.val)).op).hom s.val) := by
    have haΓ : a.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) =
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv (algebraMap S (Localization.Away g) s) := by
      exact congrArg (fun m : CommRingCat.of S ⟶ Γ(T.left, ⊤) => m.hom s)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom L.toRingHom)).symm
    change u.left.appTop (a.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) = _
    rw [haΓ]
    exact huglobal s
  obtain ⟨K, hK, hxK, GK, hGK, hevGK⟩ := s2e_curve_power_polynomial_regular_evaluation Z n x
  let PP (a : Fin b) (j : Fin (m a)) :=
    rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m (MvPolynomial.X ⟨a, j⟩)).val
  have hsection (a₀ : Fin b) (j : Fin (m a₀)) : ∀ᶠ q in 𝓝 xY,
      Point.evaluate V (G (MvPolynomial.X (ι ⟨a₀, j⟩))) (Point.map fu q) =
        Point.evaluate K (GK (PP a₀ j)) (Point.map η q) := by
    have hGKp : X.left.presheaf.germ K x.underlying hxK (GK (PP a₀ j)) =
        aeval (s2e_curvePowerParameter Z n x) (PP a₀ j) :=
      congrArg (fun F : MvPolynomial (Fin n) ℂ →+* R => F (PP a₀ j)) hGK
    have hge := s2e_open_affine_section_pullback X.left W Vg (X.left.basicOpen_le g.val)
      (CommRingCat.of S) S.val.toRingHom fu.left hglobal xY.underlying x.underlying hηunder
      z.underlying hfuunder F₀ (fun s => hF₀ s) V hzV (G (MvPolynomial.X (ι ⟨a₀, j⟩)))
      K hxK (GK (PP a₀ j)) ((hval a₀ j).trans hGKp.symm)
    have hh := s2e_equal_germs_eventually_evaluate Y xY (fu.left ⁻¹ᵁ V) (η.left ⁻¹ᵁ K)
      (by change fu.left xY.underlying ∈ V; rw [hfuunder]; exact hzV) (by change xY.underlying.val ∈ K; rw [hηunder]; exact hxK)
      (fu.left.app V (G (MvPolynomial.X (ι ⟨a₀, j⟩)))) (η.left.app K (GK (PP a₀ j))) hge
    filter_upwards [hh] with q hq
    exact (Point.evaluate_map fu V _ q).trans (hq.trans (Point.evaluate_map η K _ q).symm)
  have htU : Tendsto (Point.map u) (𝓝 xY) (𝓝 w) := by
    have ht : Tendsto (Point.map u) (𝓝 xY) (𝓝 (Point.map u xY)) :=
      (Point.continuous_map u).continuousAt.tendsto
    rwa [hux] at ht
  have htη : Tendsto (Point.map η) (𝓝 xY) (𝓝 x) := by
    have ht : Tendsto (Point.map η) (𝓝 xY) (𝓝 (Point.map η xY)) :=
      (Point.continuous_map η).continuousAt.tendsto
    rwa [hηx] at ht
  refine ⟨e, he, hez, hef, hei, ?_⟩
  have hh : ∀ᶠ q in 𝓝 xY, ∀ a₀ (j : Fin (m a₀)),
      e (Point.map γ (Point.map η q)) (ι ⟨a₀, j⟩) = aeval (fun i : Fin (m a₀) =>
        ComplexPoint.localChart Z 1 (p a₀) (Point.map (g3_proj Z n (ι ⟨a₀, i⟩)) (Point.map η q)) 0 -
          ComplexPoint.localChart Z 1 (p a₀) (p a₀) 0) (esymm (Fin (m a₀)) ℂ (j.val + 1)) := by
    filter_upwards [htU.eventually hev, htη.eventually hevGK,
      eventually_all.mpr (fun a₀ => eventually_all.mpr (hsection a₀))] with q hq hqK hqS
    intro a₀ j
    calc
      e (Point.map γ (Point.map η q)) (ι ⟨a₀, j⟩) =
          Point.evaluate V (G (MvPolynomial.X (ι ⟨a₀, j⟩))) (Point.map fu q) := by
        rw [← hbase q]
        exact hq _
      _ = Point.evaluate K (GK (PP a₀ j)) (Point.map η q) := hqS a₀ j
      _ = aeval (fun i => ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x)
          (Point.map (g3_proj Z n i) (Point.map η q)) 0 -
          ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x) (Point.map (g3_proj Z n i) x) 0) (PP a₀ j) := hqK _
      _ = _ := by
        dsimp only [PP]
        rw [s2e_mixed_polynomial_invariant_X, aeval_rename, aeval_rename]
        apply congrArg (fun r : Fin (m a₀) → ℂ => aeval r (esymm (Fin (m a₀)) ℂ (j.val + 1)))
        funext i
        simp only [Function.comp_apply]
        rw [hx a₀ i]
  have hn := s2e_open_point_eventually X Vg xY (fun q => ∀ a₀ (j : Fin (m a₀)),
    e (Point.map γ q) (ι ⟨a₀, j⟩) = aeval (fun i : Fin (m a₀) =>
      ComplexPoint.localChart Z 1 (p a₀) (Point.map (g3_proj Z n (ι ⟨a₀, i⟩)) q) 0 -
        ComplexPoint.localChart Z 1 (p a₀) (p a₀) 0) (esymm (Fin (m a₀)) ℂ (j.val + 1))) hh
  rwa [hηx] at hn

#print axioms s2e_mixed_elementary_analytic_neighbourhood
end HodgeLean.Foundations.Program
