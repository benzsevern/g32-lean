import HodgeLean.Foundations.Program.SchoenCycleC1PowerProductNaturality
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackSquare
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The descended coordinate generator satisfies the actual Kummer equation
with the symmetric coefficient through the original retained scheme square. -/
theorem s2e_c1_descended_product_kummer_equation
    (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral W.left] [IsIntegral B.left]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (p : Y ⟶ Z) (N : ℕ)
    (π : Z.left.functionField →+* Y.left.functionField)
    (hπ : ∀ x (r : Z.left.presheaf.stalk (p.left x)),
      π (algebraMap (Z.left.presheaf.stalk (p.left x)) Z.left.functionField r) =
        algebraMap (Y.left.presheaf.stalk x) Y.left.functionField ((p.left.stalkMap x).hom r))
    (φY : Fin N → (Y.left.functionField →+* (g3_power Y N).left.functionField))
    (hY : ∀ i x (r : Y.left.presheaf.stalk ((g3_proj Y N i).left x)),
      φY i (algebraMap (Y.left.presheaf.stalk ((g3_proj Y N i).left x)) Y.left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk x) (g3_power Y N).left.functionField
          (((g3_proj Y N i).left.stalkMap x).hom r))
    (φZ : Fin N → (Z.left.functionField →+* (g3_power Z N).left.functionField))
    (hZ : ∀ i x (r : Z.left.presheaf.stalk ((g3_proj Z N i).left x)),
      φZ i (algebraMap (Z.left.presheaf.stalk ((g3_proj Z N i).left x)) Z.left.functionField r) =
        algebraMap ((g3_power Z N).left.presheaf.stalk x) (g3_power Z N).left.functionField
          (((g3_proj Z N i).left.stalkMap x).hom r))
    (ρ : (g3_power Z N).left.functionField →+* (g3_power Y N).left.functionField)
    (hρ : ∀ x (r : (g3_power Z N).left.presheaf.stalk ((s2_powerMap p N).left x)),
      ρ (algebraMap ((g3_power Z N).left.presheaf.stalk ((s2_powerMap p N).left x))
        (g3_power Z N).left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk x) (g3_power Y N).left.functionField
          (((s2_powerMap p N).left.stalkMap x).hom r))
    (q : g3_power Y N ⟶ W) (γ : g3_power Z N ⟶ B) (β : W ⟶ B)
    (hsq : q ≫ β = s2_powerMap p N ≫ γ)
    (qstar : W.left.functionField →+* (g3_power Y N).left.functionField)
    (hqstar : ∀ x (r : W.left.presheaf.stalk (q.left x)),
      qstar (algebraMap (W.left.presheaf.stalk (q.left x)) W.left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk x) (g3_power Y N).left.functionField
          ((q.left.stalkMap x).hom r))
    (γstar : B.left.functionField →+* (g3_power Z N).left.functionField)
    (hγstar : ∀ x (r : B.left.presheaf.stalk (γ.left x)),
      γstar (algebraMap (B.left.presheaf.stalk (γ.left x)) B.left.functionField r) =
        algebraMap ((g3_power Z N).left.presheaf.stalk x) (g3_power Z N).left.functionField
          ((γ.left.stalkMap x).hom r))
    (βstar : B.left.functionField →+* W.left.functionField)
    (hβstar : ∀ x (r : B.left.presheaf.stalk (β.left x)),
      βstar (algebraMap (B.left.presheaf.stalk (β.left x)) B.left.functionField r) =
        algebraMap (W.left.presheaf.stalk x) W.left.functionField ((β.left.stalkMap x).hom r))
    (f : Y.left.functionField) (c : Z.left.functionField) (m : ℕ)
    (heq : f ^ m = π c) (z : W.left.functionField) (d : B.left.functionField)
    (hz : qstar z = ∏ i, φY i f) (hd : γstar d = ∏ i, φZ i c) :
    z ^ m = βstar d := by
  have hsq' : q.left ≫ β.left = (s2_powerMap p N).left ≫ γ.left :=
    congrArg Over.Hom.left hsq
  have hcomm := s2e_c1_rational_pullback_square q.left β.left (s2_powerMap p N).left
    γ.left hsq' qstar βstar ρ γstar hqstar hβstar hρ hγstar
  have heval := RingHom.congr_fun hcomm d
  change qstar (βstar d) = ρ (γstar d) at heval
  apply qstar.injective
  rw [map_pow, hz, heval, hd, s2e_c1_power_product_naturality Y Z p N π hπ φY hY φZ hZ ρ hρ c]
  rw [← Finset.prod_pow]
  simp_rw [← map_pow, heq]

end HodgeLean.Foundations.Program
