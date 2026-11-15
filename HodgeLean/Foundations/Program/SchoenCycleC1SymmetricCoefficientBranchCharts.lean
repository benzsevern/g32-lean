import HodgeLean.Foundations.Program.SchoenCycleC1NativeBranchFactorization
import HodgeLean.Foundations.Program.SchoenCycleC1PowerRationalProductOrderData
import HodgeLean.Foundations.Program.SchoenCycleC1SymmetricRationalProductDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The original curve rational product descends to a specified symmetric
coefficient with actual insertion branch factorizations near every tuple. -/
theorem s2e_c1_symmetric_coefficient_branch_charts
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] (N : ℕ)
    (γ : g3_power Z (N + 1) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z (N + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (N + 1) ⟶ T),
      (∀ σ, s2_permute Z (N + 1) σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (f : Z.left.functionField) (hf : f ≠ 0) :
    letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z (N + 1)) B γ hsurj
    let hg := s2e_c1_dominant_generic_point γ.left
    let ψ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      γ.left.stalkMap (genericPoint (g3_power Z (N + 1)).left)).hom
    ∃ (φ : Fin (N + 1) → (Z.left.functionField →+* (g3_power Z (N + 1)).left.functionField))
      (d : B.left.functionField) (n : ComplexPoint Z → ℤ),
      (∀ i, Function.Injective (φ i) ∧
        ∀ p (r : Z.left.presheaf.stalk ((g3_proj Z (N + 1) i).left p)),
          φ i (algebraMap (Z.left.presheaf.stalk ((g3_proj Z (N + 1) i).left p)) Z.left.functionField r) =
            algebraMap ((g3_power Z (N + 1)).left.presheaf.stalk p) (g3_power Z (N + 1)).left.functionField
              (((g3_proj Z (N + 1) i).left.stalkMap p).hom r)) ∧
      d ≠ 0 ∧ ψ d = ∏ i, φ i f ∧
      (∃ u : ∀ p : ComplexPoint Z, (Z.left.presheaf.stalk p.underlying)ˣ,
        ∀ p, f = algebraMap (Z.left.presheaf.stalk p.underlying) Z.left.functionField (u p : _) *
          algebraMap (Z.left.presheaf.stalk p.underlying) Z.left.functionField
            (s2e_native_curve_parameter Z p) ^ n p) ∧
      ∀ (x : ComplexPoint (g3_power Z (N + 1))) (U : B.left.Opens), γ.left x.underlying ∈ U →
        let A := Finset.univ.image (fun i => Point.map (g3_proj Z (N + 1) i) x)
        ∃ (V : B.left.affineOpens) (hxV : γ.left x.underlying ∈ V.1), V.1 ≤ U ∧
          letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
          ∃ (c : A → Γ(B.left, V.1)) (v : Γ(B.left, V.1)ˣ),
            (∀ a : A, (s2c_branchIdeal Z B N γ a.val).ideal V = Ideal.span {c a} ∧ c a ≠ 0) ∧
            d = B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) *
              ∏ a : A, (B.left.germToFunctionField V.1 (c a)) ^ n a.val := by
  letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z (N + 1)) B γ hsurj
  dsimp only
  obtain ⟨φ, hφ, hprod, n, hcurve, hn⟩ := s2e_c1_power_rational_product_order_data Z (N + 1) f hf
  obtain ⟨d, hd⟩ := s2e_c1_symmetric_rational_product_descent Z B (N + 1) γ hγ hquot
    φ (fun i => (hφ i).2) f
  refine ⟨φ, d, n, hφ, ?_, hd, hcurve, ?_⟩
  · intro he
    apply hprod
    rw [← hd, he, map_zero]
  · intro x U hx
    let A := Finset.univ.image (fun i => Point.map (g3_proj Z (N + 1) i) x)
    let g (i : Fin (N + 1)) : A := ⟨Point.map (g3_proj Z (N + 1) i) x,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    apply s2e_c1_native_branch_factorization Z B N γ hsurj hγ hquot x
      (fun a : A => a.val) Subtype.val_injective g (fun _ => rfl) (fun a : A => n a.val) d U hx
    obtain ⟨u, hu⟩ := hn x
    exact ⟨u, hd.trans hu⟩

end HodgeLean.Foundations.Program
