import HodgeLean.Foundations.Program.SchoenTransferE1CoordinateAction
import HodgeLean.Foundations.Program.SchoenTransferE1CurveRepresentation
import HodgeLean.Foundations.Program.SchoenTransferE1Simultaneous

/-! The actual coordinate deck representation in each degree of a curve power. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters

attribute [local instance] Classical.propDecidable

namespace HodgeLean.Foundations.Program

/-- Coordinate deck pullbacks form the actual rational tuple-group representation.
Source: Schoen (1988), §1, p. 5; the actual coordinate action and pullback functoriality. -/
def s4_e1_deckPullbackRepresentation
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (h n : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    Multiplicative (Fin h → ZMod S.m) →* Module.End ℚ (HQ (g3_power Y h) n) :=
  s4_e1_curvePullbackRepresentation (g3_power Y h)
    (fun v : Multiplicative (Fin h → ZMod S.m) => s2_action S Y a e h v.toAdd 1)
    (s4_e1_deck_action_zero S Y a e ha1 h)
    (fun v w => (s4_e1_deck_action_add S Y a e hamul h v.toAdd w.toAdd).symm) n

/-- Every actual deck-tuple pullback satisfies the supplied cyclic order relation.
Source: Schoen (1988), §1, p. 5; each tuple coordinate is in the same cyclic group. -/
theorem s4_e1_deckPullback_pow
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (h n : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (v : Multiplicative (Fin h → ZMod S.m)) :
    s4_e1_deckPullbackRepresentation S Y a e ha1 hamul h n v ^ S.m = 1 := by
  have hv : v ^ S.m = 1 := by
    change Multiplicative.ofAdd (S.m • v.toAdd) = Multiplicative.ofAdd 0
    apply congrArg Multiplicative.ofAdd
    funext i
    change S.m • v.toAdd i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← map_pow, hv, map_one]

/-- The actual deck-tuple pullbacks commute.
Source: Schoen (1988), §1, p. 5; commutativity of the coordinate cyclic groups. -/
theorem s4_e1_deckPullback_commute
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (h n : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (v w : Multiplicative (Fin h → ZMod S.m)) :
    Commute (s4_e1_deckPullbackRepresentation S Y a e ha1 hamul h n v)
      (s4_e1_deckPullbackRepresentation S Y a e ha1 hamul h n w) := by
  let ρ := s4_e1_deckPullbackRepresentation S Y a e ha1 hamul h n
  change ρ v * ρ w = ρ w * ρ v
  rw [← map_mul, ← map_mul, mul_comm v w]

set_option maxHeartbeats 400000 in
/-- The actual coordinate operators on complexified power cohomology have an
internal decomposition into simultaneous root-of-unity character spaces.
Source: Schoen (1988), Lemma 1.2, pp. 5–6; the actual deck representation. -/
theorem s4_e1_power_character_decomposition
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (h n : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    DirectSum.IsInternal (fun c : Fin h → rootsOfUnity S.m ℂ =>
      ⨅ i, Module.End.eigenspace
        ((s4_e1_deckPullbackRepresentation S Y a e ha1 hamul h n
          (.ofAdd (Pi.single i 1))).baseChange ℂ) ((c i : ℂˣ) : ℂ)) := by
  letI : Module.Finite ℚ (HQ (g3_power Y h) n) :=
    (finbetti_finiteBetti (g3_power Y h)).finite n
  let ρ := s4_e1_deckPullbackRepresentation S Y a e ha1 hamul h n
  let f (i : Fin h) : Module.End ℂ (ℂ ⊗[ℚ] HQ (g3_power Y h) n) :=
    (ρ (.ofAdd (Pi.single i 1))).baseChange ℂ
  have hf (i : Fin h) : f i ^ S.m = 1 := by
    dsimp only [f, ρ]
    rw [← LinearMap.baseChange_pow, s4_e1_deckPullback_pow,
      Module.End.one_eq_id, LinearMap.baseChange_id]
    rfl
  have hc (i j : Fin h) : Commute (f i) (f j) :=
    (s4_e1_deckPullback_commute S Y a e ha1 hamul h n
      (.ofAdd (Pi.single i 1)) (.ofAdd (Pi.single j 1))).map
        (Module.End.baseChangeHom ℚ ℂ (HQ (g3_power Y h) n))
  exact s4_e1_simultaneous_root_decomposition (m := S.m) f
    (lt_of_lt_of_le (by decide : 0 < 3) S.three_le) hf hc

#print axioms s4_e1_deckPullbackRepresentation
#print axioms s4_e1_deckPullback_pow
#print axioms s4_e1_deckPullback_commute
#print axioms s4_e1_power_character_decomposition
end HodgeLean.Foundations.Program
