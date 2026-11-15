import HodgeLean.Foundations.Program.SchoenTransferJ1Row1Proofs
import HodgeLean.Foundations.Program.SchoenTransferJ1Row4Proofs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A retained quotient basis supplies curve-power cycles after its specified degree reindexing. -/
theorem s4_selected_quotient_basis_cycles
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n k : ℕ) (hk : 0 < k)
    (hn : 0 < n) (hdegree : n = 2 * k)
    [IsIntegral (g3_power Y (2 * k)).left]
    [Smooth (g3_power Y (2 * k)).hom] [IsProjective (g3_power Y (2 * k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y n ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hquot : ∀ (Z : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ Z),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! g : W ⟶ Z, q ≫ g = f)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (b : Fin (Nat.totient S.m) →
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k))
    (hb : Submodule.span ℚ (Set.range b) = LinearMap.ker
      (Polynomial.aeval (s4_singularPullback d (2 * k)) (Polynomial.cyclotomic S.m ℚ)))
    (hcycles : ∀ i, ∃ z : AlgebraicCycle W.left ℚ,
      (∀ x ∈ z.support, Order.coheight x = k ∧
        ∃ U : W.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W.hom)) ∧
      ∃ c, a3b4_IsCycleClass W.hom z k c ∧ s2e_classToAbsolute W z k c = b i) :
    s4_invariantPrimitive S Y a e (2 * k) (Nat.mul_pos (by norm_num) hk) ≤
      cfd_cycleSpan (g3_power Y (2 * k)) k := by
  subst n
  have hforward : ∀ u v, a (u * v) = a u ≫ a v := by
    intro u v
    have hcomm : u * v = v * u := e.injective (by rw [map_mul, map_mul, mul_comm])
    rw [hcomm, hamul]
  have hfib := s4_chain_selected_quotient_fibre_orbits_aux S Y a e ha1 hamul
    (2 * k) W q hqsurj hqinv hquot
  exact (s4_chain_selected_curve_invariant_cycles_aux S Y hdim k hk a e ha1 hforward
    W q hqsurj hqinv hfib d hgenerator.symm b hb hcycles).2

#print axioms s4_selected_quotient_basis_cycles

end HodgeLean.Foundations.Program
