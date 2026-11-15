import HodgeLean.Foundations.Program.SchoenCycleC1InitialKummerBranchData
import HodgeLean.Foundations.Program.SchoenCycleC1InitialSpecifiedKummerBasis
import HodgeLean.Foundations.Program.SchoenCycleC1RetainedProjectionSurjective
import HodgeLean.Foundations.Program.SchoenCycleC1UnmarkedCoefficientOrder
import HodgeLean.Foundations.Program.SchoenCycleC1SignedUnmarkedFactors

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Polynomial
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The original curve action, branch criterion and quotient square construct
actual affine branch charts whose scaled original generator is a power basis
with exactly the marked coefficient factors. No unmarked divisibility or
generic degree computation is supplied separately. -/
theorem s2e_c1_initial_marked_kummer_charts
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [SmoothOfRelativeDimension 1 Z.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1) (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) [IsFinite p.left] (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (T I : Type) [Finite I] [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i)
    (N : ℕ) (hh : 0 < N + 1)
    (q : g3_power Y (N + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (N + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (N + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (N + 1) v τ ≫ q = q)
    (hq : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Y (N + 1) ⟶ A),
      (∀ (v : Fin (N + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (N + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (N + 1) v τ ≫ f = f) →
      ∃! u : W ⟶ A, q ≫ u = f)
    (γ : g3_power Z (N + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (N + 1) τ ≫ γ = γ)
    (hγ : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Z (N + 1) ⟶ A),
      (∀ τ, s2_permute Z (N + 1) τ ≫ f = f) → ∃! u : B ⟶ A, γ ≫ u = f)
    (β : W ⟶ B) [IsFinite β.left] (hβ : q ≫ β = s2_powerMap p (N + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ S.m = 1)
    (hgenerator : q ≫ d = s2_action S Y a e (N + 1) (s2_delta S (N + 1) hh 1) 1 ≫ q)
 :
    letI : Surjective β.left := s2e_c1_retained_projection_surjective
      Y Z W B p hpsurj (N + 1) q γ hγsurj β hβ
    letI : Surjective p.left := s2e_c11_surjective_of_point_surjective Y Z p hpsurj
    let hpgen := s2_dominant_genericPoint p.left
    let π := (eqToHom (congrArg Z.left.presheaf.stalk hpgen.symm) ≫
      p.left.stalkMap (genericPoint Y.left)).hom
    let hg := s2e_c1_dominant_generic_point β.left
    let βstar := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      β.left.stalkMap (genericPoint W.left)).hom
    ∃ (χ : Multiplicative (ZMod S.m) →* ℂˣ)
      (f : Y.left.functionField) (c : Z.left.functionField) (z : W.left.functionField)
      (d₀ : B.left.functionField) (n : ComplexPoint Z → ℤ),
      Function.Injective χ ∧ f ≠ 0 ∧ c ≠ 0 ∧ z ≠ 0 ∧ d₀ ≠ 0 ∧
      f ^ S.m = π c ∧ z ^ S.m = βstar d₀ ∧
      (∀ t : ZMod S.m,
        letI := s2e_step1_action_isIso Y (S.H ⧸ S.χ.ker) a ha1 hamul (e.symm (.ofAdd t))
        s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd t))).left f =
          HodgeLean.Foundations.Curves.stalkC (genericPoint Y.left) (χ (.ofAdd t) : ℂ) * f) ∧
      (∃ u : ∀ x : ComplexPoint Z, (Z.left.presheaf.stalk x.underlying)ˣ,
        ∀ x, c = algebraMap _ Z.left.functionField (u x : Z.left.presheaf.stalk x.underlying) *
          algebraMap _ Z.left.functionField (s2e_native_curve_parameter Z x) ^ n x) ∧
      (∀ x : ComplexPoint Z, (∀ i, x ≠ marks i) → (S.m : ℤ) ∣ n x) ∧
      ∀ (x : ComplexPoint (g3_power Z (N + 1))) (U : B.left.Opens), γ.left x.underlying ∈ U →
        let A := Finset.univ.image (fun i => Point.map (g3_proj Z (N + 1) i) x)
        ∃ (V : B.left.affineOpens) (hxV : γ.left x.underlying ∈ V.1), V.1 ≤ U ∧
          letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
          ∃ (b : A → Γ(B.left, V.1)) (v : Γ(B.left, V.1)ˣ) (α : B.left.functionField),
            (∀ j : A, (s2c_branchIdeal Z B N γ j.val).ideal V = Ideal.span {b j} ∧ b j ≠ 0) ∧
            α ≠ 0 ∧
            d₀ = α ^ S.m * (B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) *
              ∏ j ∈ Finset.univ.filter (fun j : A => ∃ i, j.val = marks i),
                (B.left.germToFunctionField V.1 (b j)) ^ n j.val) ∧
            let cV : B.left.functionField :=
              B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) *
                ∏ j ∈ Finset.univ.filter (fun j : A => ∃ i, j.val = marks i),
                  (B.left.germToFunctionField V.1 (b j)) ^ n j.val
            letI := βstar.toAlgebra
            ∃ P : PowerBasis B.left.functionField W.left.functionField,
              P.gen = z / βstar α ∧
              P.dim = S.m ∧ (z / βstar α) ^ S.m = βstar cV := by
  letI : Surjective β.left := s2e_c1_retained_projection_surjective
    Y Z W B p hpsurj (N + 1) q γ hγsurj β hβ
  letI : Surjective p.left := s2e_c11_surjective_of_point_surjective Y Z p hpsurj
  letI : IsIso d := by
    simpa only [pow_one] using s2e_generator_power_isIso d (NeZero.ne S.m) horder 1
  let hg := s2e_c1_dominant_generic_point β.left
  let βstar := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
    β.left.stalkMap (genericPoint W.left)).hom
  letI := βstar.toAlgebra
  obtain ⟨χ, f, c, z, d₀, n, hχ, hf, hc, hz, hd₀, hfc, hpower, heig, heigen, hcurve, hcharts⟩ :=
    s2e_c1_initial_kummer_branch_data S Y Z W B a e ha1 hamul hinj p hpsurj hp hporbit
      N q hqsurj hqinv hq γ hγsurj hγinv hγ β hβ d hgenerator
  obtain ⟨u, hu⟩ := hcurve
  have hdiv (x : ComplexPoint Z) (hx : ∀ i, x ≠ marks i) : (S.m : ℤ) ∣ n x :=
    s2e_c1_unmarked_coefficient_order_dvd Y Z hdimY hdimZ (S.H ⧸ S.χ.ker)
      a ha1 hamul hinj p hpsurj hp hporbit T I eY hpointAction marks hbranch
      (s2_dominant_genericPoint p.left) c f hf S.m n u hu hfc x hx
  refine ⟨χ, f, c, z, d₀, n, hχ, hf, hc, hz, hd₀, hfc, hpower, heig, ⟨u, hu⟩, hdiv, ?_⟩
  intro x U hx
  obtain ⟨V, hxV, hVU, b, v, hb, hdV⟩ := hcharts x U hx
  letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
  let A := Finset.univ.image (fun i => Point.map (g3_proj Z (N + 1) i) x)
  have hbK (j : A) : B.left.germToFunctionField V.1 (b j) ≠ 0 := by
    intro he
    exact (hb j).2 (B.left.germToFunctionField_injective V.1 (he.trans (map_zero _).symm))
  obtain ⟨α, hα, hfactor, hz', hp'⟩ := s2e_c1_signed_unmarked_factors
    βstar z hz S.m (fun j : A => B.left.germToFunctionField V.1 (b j)) hbK
    (fun j : A => n j.val) (fun j : A => ∃ i, j.val = marks i)
    (fun j hj => hdiv j.val (fun i hi => hj ⟨i, hi⟩))
    (B.left.germToFunctionField V.1 (v : Γ(B.left, V.1))) (hpower.trans (congrArg βstar hdV))
  have hfix := s2e_c1_fieldPullback_fixes_base β.left βstar
    (s2e_c1_genericStalkMap_square β.left hg) d.left (congrArg Over.Hom.left hd)
  have heigen' : s2e_step1_fieldPullback W.left d.left (z / βstar α) =
      HodgeLean.Foundations.Curves.stalkC (genericPoint W.left) (χ (.ofAdd 1) : ℂ) *
        (z / βstar α) := by
    rw [map_div₀, heigen]
    have he := RingHom.congr_fun hfix α
    change s2e_step1_fieldPullback W.left d.left (βstar α) = βstar α at he
    rw [he, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  obtain ⟨P, hP, hmin⟩ := s2e_c1_initial_specified_kummer_basis
    S Y Z W B a e ha1 hamul hinj p hp hpsurj hporbit T I eY hpointAction marks hbranch
    N hh q hqsurj hqinv hq γ hγsurj hγinv hγ β hβ d hd horder hgenerator
    χ hχ (z / βstar α) hz' _ heigen' hp'
  refine ⟨V, hxV, hVU, b, v, α, hb, hα, hdV.trans hfactor, P, hP, ?_, hp'⟩
  rw [← P.natDegree_minpoly, hmin, Polynomial.natDegree_X_pow_sub_C]

end HodgeLean.Foundations.Program
