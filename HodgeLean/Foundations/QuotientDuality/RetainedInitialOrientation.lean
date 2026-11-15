import HodgeLean.Foundations.QuotientDuality.RetainedQuotientHomeomorph
import HodgeLean.Foundations.QuotientDuality.LocalAlgebraicOrbitOrientation
import HodgeLean.Foundations.QuotientDuality.LocalOrientationTransport
import HodgeLean.Foundations.QuotientDuality.LocalBasisTransport
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import HodgeLean.Adapters.AbelianPower

/-! Coherent local orientation and an actual pushed class on the retained initial quotient. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations
open HodgeLean.Foundations.Analytic
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_initial_coherent_orientation
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (q : g3_power Y n ⟶ W) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)
    (hdim : dim Y.left = 1) :
    ∃ (cP : Homology ℚ (TopCat.of (ComplexPoint (g3_power Y n))) (2 * n))
      (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * n))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * n)),
      (∀ (I : SmoothOfRelativeDimension n (g3_power Y n).hom) (x : ComplexPoint (g3_power Y n)),
        localOrientation (TopCat.of (ComplexPoint (g3_power Y n))) (2 * n) cP x =
          @complexLocalOrientation (g3_power Y n) n I x) ∧
      homologyMap ℚ (2 * n) (TopCat.ofHom (Point.continuousMap q)) cP =
        (Fintype.card (retainedCoordinateSubgroup S Y a e ha1 hamul n) : ℚ) • c ∧
      ∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * n) c x = o.generator x := by
  letI := spec_g3b_geometricallyIntegral Y
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdim]; infer_instance
  let P := g3_power Y n
  letI : SmoothOfRelativeDimension n P.hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power Y 1 n
  let G := retainedCoordinateSubgroup S Y a e ha1 hamul n
  let Q := orbitSpace G (TopCat.of (ComplexPoint P))
  obtain ⟨H, hH⟩ := retained_coordinate_quotient_homeomorph S Y W a e ha1 hamul n q hsurj hinv hquot
  letI : SecondCountableTopology (ComplexPoint W) := f4_secondCountable W
  letI : PseudoMetrizableSpace (ComplexPoint W) := inferInstance
  letI : T2Space Q := H.isEmbedding.t2Space
  letI : PseudoMetrizableSpace Q := H.isInducing.pseudoMetrizableSpace
  have hQ := homeomorph_contractible_basis H (ComplexTopology.finiteType_basis W)
  obtain ⟨cP, oQ, cQ, hcP, hdegree, hcQ⟩ := smooth_algebraic_orbit_orientation P n G
    (fun g => g.val.asIso) (fun _ _ => rfl) hQ (Fintype.card G) Fintype.card_pos
  let fH : Q ⟶ TopCat.of (ComplexPoint W) := TopCat.ofHom ⟨H, H.continuous⟩
  obtain ⟨o, hc, _⟩ := homeomorph_pushforward_coherent_orientation Q
    (TopCat.of (ComplexPoint W)) (2 * n) oQ cQ hcQ H
  refine ⟨cP, o, homologyMap ℚ (2 * n) fH cQ, (fun _ => hcP), ?_, hc⟩
  have hqmap : orbitMap G (TopCat.of (ComplexPoint P)) ≫ fH =
      TopCat.ofHom (Point.continuousMap q) := by
    ext x
    exact congrArg Over.Hom.left (hH x)
  rw [← hqmap, homologyMap_comp, LinearMap.comp_apply, hdegree, map_smul]

#print axioms retained_initial_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
