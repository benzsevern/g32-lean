import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericPoint
import HodgeLean.Foundations.Program.SchoenCycleC1ActualSpecifiedKummerBasis
import HodgeLean.Foundations.Program.SchoenCycleC1InitialMeasuredFibres
import HodgeLean.Foundations.Program.SchoenCycleC1InitialFaithfulHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFieldDegreeHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Polynomial
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The original measured fibres and residual action make the specified
descended eigenfunction itself an exact Kummer power basis. The field degree
and absence of shorter deck periods are derived from the original geometry. -/
theorem s2e_c1_initial_specified_kummer_basis
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (T I : Type*) [Finite I] [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i)
    (h : ℕ) (hh : 0 < h + 1)
    (q : g3_power Y (h + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q = q)
    (hq : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ A),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W ⟶ A, q ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ A),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ A, γ ≫ u = f)
    (β : W ⟶ B) [IsFinite β.left] [Surjective β.left] (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ S.m = 1)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)

    (χ : Multiplicative (ZMod S.m) →* ℂˣ) (hχ : Function.Injective χ)
    (z : W.left.functionField) (hz : z ≠ 0) (c : B.left.functionField)
    (heig :
      letI : IsIso d := by
        simpa only [pow_one] using s2e_generator_power_isIso d (NeZero.ne S.m) horder 1
      s2e_step1_fieldPullback W.left d.left z =
        HodgeLean.Foundations.Curves.stalkC (genericPoint W.left) (χ (.ofAdd 1) : ℂ) * z) :
    let hg := s2e_c1_dominant_generic_point β.left
    let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      β.left.stalkMap (genericPoint W.left)).hom
    letI := φ.toAlgebra
    z ^ S.m = φ c →
    ∃ P : PowerBasis B.left.functionField W.left.functionField,
      P.gen = z ∧ minpoly B.left.functionField P.gen = X ^ S.m - C c := by
  letI : IsIso d := by
    simpa only [pow_one] using s2e_generator_power_isIso d (NeZero.ne S.m) horder 1
  let hg := s2e_c1_dominant_generic_point β.left
  let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
    β.left.stalkMap (genericPoint W.left)).hom
  letI := φ.toAlgebra
  dsimp only
  intro hpower
  have hdim : Module.finrank B.left.functionField W.left.functionField = S.m :=
    s2e_c1_actual_fieldDegree_of_measured_fibres W B β hg S.m
      (s2e_c1_initial_measured_fibres S Y Z W B a e ha1 hamul hinj p hp hpsurj hporbit
        T I eY hpointAction marks hbranch h hh q hqsurj hqinv hq γ hγsurj hγinv hγ
        β hβ d hd horder hgenerator)
  have hfaith := s2e_c1_initial_generator_faithful_powers S Y Z W a e ha1 hamul hinj
    p hp hporbit (h + 1) hh q hqsurj hqinv hq d hgenerator
  let F : End W →* End W.left := (Over.forget (Spec ↧ℂ)).mapEnd W
  have hF : Function.Injective F := by
    intro a b hab
    apply End.ext
    apply Over.OverMorphism.ext
    exact congrArg End.asHom hab
  have hpowL : End.of d.left ^ S.m = 1 := by
    have he := congrArg F horder
    simp only [map_pow, map_one] at he
    change End.of d.left ^ S.m = 1 at he
    exact he
  have hfaithL (n : ℕ) (hn : n < S.m) (he : End.of d.left ^ n = 1) : n = 0 := by
    apply hfaith n hn
    apply hF
    rw [map_pow, map_one]
    exact he
  let ψ : Multiplicative (ZMod S.m) →* ℂ := (Units.coeHom ℂ).comp χ
  have hroot : IsPrimitiveRoot (χ (.ofAdd 1) : ℂ) S.m := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    exact (orderOf_injective ψ (Units.val_injective.comp hχ) (.ofAdd 1)).trans
      ((orderOf_ofAdd_eq_addOrderOf (1 : ZMod S.m)).trans (ZMod.addOrderOf_one S.m))
  exact s2e_c1_actual_specified_kummer_basis W B β hg d hd S.m (NeZero.pos S.m)
    hpowL hfaithL (χ (.ofAdd 1) : ℂ) hroot z hz c heig hdim hpower

end HodgeLean.Foundations.Program
