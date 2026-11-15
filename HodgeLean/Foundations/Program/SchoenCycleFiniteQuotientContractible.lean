import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientLocalLinearization
import HodgeLean.Foundations.Program.FiniteQuotientContraction
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

/-! # Contractible neighborhoods in the actual finite quotient
The target may be singular; contractions descend from stabilizer charts.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual finite quotient of the smooth source has a contractible open basis.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3; Takamura, Linearization of Quotient Families,
J. Math. Sci. Univ. Tokyo 26 (2019), pp. 380–382, finite stabilizer charts. -/
theorem s2e_finite_quotient_target_contractibleOpen_basis
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ T, q ≫ g = f)
    (y₀ : ComplexPoint Y) (N : Opens (ComplexPoint Y)) (hyN : y₀ ∈ N) :
    ∃ V : Opens (ComplexPoint Y), y₀ ∈ V ∧ ContractibleSpace V ∧ V ≤ N := by
  classical
  obtain ⟨x₀, rfl⟩ := hsurj y₀
  letI := s2e_quotientPointMulAction X G a ha1 hamul
  let K := MulAction.stabilizer G x₀
  let M : Opens (ComplexPoint X) :=
    ⟨(Point.map q) ⁻¹' (N : Set (ComplexPoint Y)), N.isOpen.preimage (Point.continuous_map q)⟩
  obtain ⟨V, hxV, hVM, hVi, hVorb, ρ, e, W, he0, hVsource,
      hWo, hW0, hWconv, hImage, hWi, hEq⟩ :=
    s2e_finite_quotient_stabilizer_convex_coordinates X Y (dim X.left) G a ha1 hamul q
      hsurj hinv hquot x₀ M hyN
  let S : SubMulAction K (ComplexPoint X) := {
    carrier := V
    smul_mem' := fun g x hx => hVi g x hx }
  have hstar : StarConvex ℝ (0 : Fin (dim X.left) → ℂ) (e '' (S : Set (ComplexPoint X))) := by
    change StarConvex ℝ (0 : Fin (dim X.left) → ℂ) (e '' (V : Set (ComplexPoint X)))
    rw [hImage]
    exact hWconv.starConvex hW0
  obtain ⟨H, hHeq⟩ := equivariant_chart_radial_contraction K S e hVsource ⟨x₀, hxV⟩ he0
    hstar ρ (fun g x => hEq g x x.property)
  have hqopen : IsOpenMap (Point.map q) :=
    s2e_finite_quotient_pointMap_isOpenMap X Y G a ha1 hamul q hsurj hinv hquot
  let R : Set (ComplexPoint Y) := Point.map q '' (V : Set (ComplexPoint X))
  let p : C(S, R) :=
    ⟨fun x => ⟨Point.map q x, ⟨x, x.property, rfl⟩⟩,
      ((Point.continuous_map q).comp continuous_subtype_val).subtype_mk _⟩
  have hi : IsOpenMap (Subtype.val : S → ComplexPoint X) := V.isOpen.isOpenMap_subtype_val
  have hpop : IsOpenMap p :=
    (hqopen.comp hi).codRestrict (s := R) (fun x => ⟨x, x.property, rfl⟩)
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨x, hx, he⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hpq : IsOpenQuotientMap p := ⟨hpsurj, p.continuous, hpop⟩
  have hcontract : ContractibleSpace R := by
    apply open_quotient_contractible_of_fibre_preserving_contraction p hpq ⟨x₀, hxV⟩ H
    intro t x y hxy
    have he : Point.map q (x : ComplexPoint X) = Point.map q (y : ComplexPoint X) :=
      congrArg Subtype.val hxy
    obtain ⟨g, hg⟩ := hVorb x x.property y y.property he
    have hs : g • x = y := Subtype.ext hg
    rw [← hs, hHeq]
    apply Subtype.ext
    change Point.map q (H (t, x) : ComplexPoint X) =
      Point.map q (Point.map (a g) (H (t, x) : ComplexPoint X))
    rw [← Point.map_comp_apply, hinv g]
  refine ⟨⟨R, hqopen _ V.isOpen⟩, ⟨x₀, hxV, rfl⟩, hcontract, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hVM hx

/-- The actual quotient target has the singular-cochain resolution of its constant
rational sheaf, including when the target is singular.
Source: Bredon, Sheaf Theory, second edition, Chapter II, singular-cochain
resolutions on spaces with a contractible open basis. -/
theorem s2e_finite_quotient_target_singular_cochain_resolution
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ T, q ≫ g = f) :
    QuasiIso
      (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint Y))) := by
  exact AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis
    ℚ (X := TopCat.of (ComplexPoint Y))
    (fun y U hy => s2e_finite_quotient_target_contractibleOpen_basis
      X Y G a ha1 hamul q hsurj hinv hquot y U hy)

/-- Every open subset of the actual quotient target is paracompact.
Second countability and local compactness descend from the smooth source along
the actual open quotient map; smoothness of the target is unnecessary.
Source: Bredon, Sheaf Theory, second edition, Chapter I, paracompact spaces;
Mathlib, `Topology.IsOpenQuotientMap.secondCountableTopology`. -/
theorem s2e_finite_quotient_target_openParacompactSpace
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ T, q ≫ g = f)
    (U : Opens (ComplexPoint Y)) : ParacompactSpace U := by
  letI : SecondCountableTopology (ComplexPoint X) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin (dim X.left) → ℂ) (ComplexPoint X)
  letI : LocallyCompactSpace (ComplexPoint X) :=
    ChartedSpace.locallyCompactSpace (Fin (dim X.left) → ℂ) (ComplexPoint X)
  have hq : IsOpenQuotientMap (Point.map q) :=
    ⟨hsurj, Point.continuous_map q,
      s2e_finite_quotient_pointMap_isOpenMap X Y G a ha1 hamul q hsurj hinv hquot⟩
  letI : SecondCountableTopology (ComplexPoint Y) :=
    Topology.IsOpenQuotientMap.secondCountableTopology hq
  letI : LocallyCompactSpace (ComplexPoint Y) := hq.locallyCompactSpace
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace U := inferInstance
  infer_instance

end HodgeLean.Foundations.Program
