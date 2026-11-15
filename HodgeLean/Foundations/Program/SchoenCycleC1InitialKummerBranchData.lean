import HodgeLean.Foundations.Program.SchoenCycleC1RetainedCurveKummerCharacter
import HodgeLean.Foundations.Program.SchoenCycleC1SymmetricCoefficientBranchCharts
import HodgeLean.Foundations.Program.SchoenCycleC1RetainedRationalProductDescent
import HodgeLean.Foundations.Program.SchoenCycleC1DescendedProductKummerEquation
import HodgeLean.Foundations.Program.SchoenCycleC1DescendedProductEigencharacter
import HodgeLean.Foundations.Program.SchoenCycleC1PowerMapRationalPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The original curve action and both actual quotients construct a single
Kummer generator and symmetric coefficient with native insertion-branch
charts and the specified residual deck eigenidentity. -/
theorem s2e_c1_initial_kummer_branch_data
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom]
    [IsIntegral W.left] [LocallyOfFiniteType W.hom] [IsIntegral B.left] [Smooth B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (p : Y ⟶ Z) [IsFinite p.left]
    (hpsurj : Function.Surjective (Point.map p))
    (hpinv : ∀ u, a u ≫ p = p)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (N : ℕ) (q : g3_power Y (N + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ v σ, ∑ i, v i = 0 → s2_action S Y a e (N + 1) v σ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Y (N + 1) ⟶ T),
      (∀ w σ, ∑ i, w i = 0 → s2_action S Y a e (N + 1) w σ ≫ v = v) →
        ∃! u : W ⟶ T, q ≫ u = v)
    (γ : g3_power Z (N + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (N + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (N + 1) ⟶ T),
      (∀ σ, s2_permute Z (N + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (β : W ⟶ B) [IsFinite β.left] [Surjective β.left]
    (hsq : q ≫ β = s2_powerMap p (N + 1) ≫ γ)
    (δ : W ⟶ W) [IsIso δ]
    (hδ : q ≫ δ = s2_action S Y a e (N + 1) (s2_delta S (N + 1) (by omega) 1) 1 ≫ q) :
    letI : Surjective p.left := s2e_c11_surjective_of_point_surjective Y Z p hpsurj
    let hpgen := s2_dominant_genericPoint p.left
    let π := (eqToHom (congrArg Z.left.presheaf.stalk hpgen.symm) ≫
      p.left.stalkMap (genericPoint Y.left)).hom
    let hβgen := s2e_c1_dominant_generic_point β.left
    let βstar := (eqToHom (congrArg B.left.presheaf.stalk hβgen.symm) ≫
      β.left.stalkMap (genericPoint W.left)).hom
    ∃ (χ : Multiplicative (ZMod S.m) →* ℂˣ)
      (f : Y.left.functionField) (c : Z.left.functionField)
      (z : W.left.functionField) (d : B.left.functionField) (n : ComplexPoint Z → ℤ),
      Function.Injective χ ∧ f ≠ 0 ∧ c ≠ 0 ∧ z ≠ 0 ∧ d ≠ 0 ∧
      f ^ S.m = π c ∧ z ^ S.m = βstar d ∧
      (∀ t : ZMod S.m,
        letI := s2e_step1_action_isIso Y (S.H ⧸ S.χ.ker) a ha1 hamul (e.symm (.ofAdd t))
        s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd t))).left f =
          HodgeLean.Foundations.Curves.stalkC (genericPoint Y.left) (χ (.ofAdd t) : ℂ) * f) ∧
      s2e_step1_fieldPullback W.left δ.left z =
        HodgeLean.Foundations.Curves.stalkC (genericPoint W.left) (χ (.ofAdd 1) : ℂ) * z ∧
      (∃ u : ∀ x : ComplexPoint Z, (Z.left.presheaf.stalk x.underlying)ˣ,
        ∀ x, c = algebraMap _ Z.left.functionField (u x : Z.left.presheaf.stalk x.underlying) *
          algebraMap _ Z.left.functionField (s2e_native_curve_parameter Z x) ^ n x) ∧
      ∀ (x : ComplexPoint (g3_power Z (N + 1))) (U : B.left.Opens), γ.left x.underlying ∈ U →
        let A := Finset.univ.image (fun i => Point.map (g3_proj Z (N + 1) i) x)
        ∃ (V : B.left.affineOpens) (hxV : γ.left x.underlying ∈ V.1), V.1 ≤ U ∧
          letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
          ∃ (b : A → Γ(B.left, V.1)) (v : Γ(B.left, V.1)ˣ),
            (∀ j : A, (s2c_branchIdeal Z B N γ j.val).ideal V = Ideal.span {b j} ∧ b j ≠ 0) ∧
            d = B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) *
              ∏ j : A, (B.left.germToFunctionField V.1 (b j)) ^ n j.val := by
  letI : Surjective p.left := s2e_c11_surjective_of_point_surjective Y Z p hpsurj
  letI : Surjective q.left := s2e_c11_surjective_of_point_surjective (g3_power Y (N + 1)) W q hqsurj
  letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z (N + 1)) B γ hγsurj
  obtain ⟨χ, hχ, f, c, hf, hc, hfc, heig⟩ :=
    s2e_c1_retained_curve_kummer_character S Y Z a e ha1 hamul hinj p hpsurj hpinv hporbit
  obtain ⟨φZ, d, n, hZ, hd, hprodZ, hcurve, hcharts⟩ :=
    s2e_c1_symmetric_coefficient_branch_charts Z B N γ hγsurj hγinv hγ c hc
  obtain ⟨φY, hY⟩ := s2e_c1_power_generic_field_maps Y (N + 1)
  obtain ⟨z, hprodY⟩ := s2e_c1_retained_rational_product_descent
    S Y W a e ha1 hamul (N + 1) φY (fun i => (hY i).2) χ f heig q hqinv hq
  let hqgen := s2e_c1_dominant_generic_point q.left
  let qstar := (eqToHom (congrArg W.left.presheaf.stalk hqgen.symm) ≫
    q.left.stalkMap (genericPoint (g3_power Y (N + 1)).left)).hom
  have hz : z ≠ 0 := by
    intro he
    have hp : (∏ i, φY i f) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero (φY i)).mpr hf
    apply hp
    rw [← hprodY, he, map_zero]
  obtain ⟨ρ, _, hρ⟩ := s2e_c1_power_map_rational_pullback Y Z p hpsurj (N + 1)
  have hpower := s2e_c1_descended_product_kummer_equation Y Z W B p (N + 1) _
    (s2e_c1_generic_stalk_map_local_square p.left (s2_dominant_genericPoint p.left))
    φY (fun i => (hY i).2) φZ (fun i => (hZ i).2) ρ hρ q γ β hsq
    qstar (s2e_c1_generic_stalk_map_local_square q.left hqgen)
    _ (s2e_c1_generic_stalk_map_local_square γ.left (s2e_c1_dominant_generic_point γ.left))
    _ (s2e_c1_generic_stalk_map_local_square β.left (s2e_c1_dominant_generic_point β.left))
    f c S.m hfc z d hprodY hprodZ
  have heigen := s2e_c1_descended_product_eigencharacter S Y W a e ha1 hamul
    (N + 1) φY (fun i => (hY i).2) χ f heig (by omega) q δ hδ qstar
    (s2e_c1_generic_stalk_map_local_square q.left hqgen) z hprodY
  exact ⟨χ, f, c, z, d, n, hχ, hf, hc, hz, hd, hfc, hpower, heig, heigen, hcurve, hcharts⟩

end HodgeLean.Foundations.Program
