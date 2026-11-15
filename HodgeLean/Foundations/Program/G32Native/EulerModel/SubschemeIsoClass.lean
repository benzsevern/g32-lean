import HodgeLean.Foundations.Program.G32Native.EulerModel.SubschemeIsoCycle
import HodgeLean.Foundations.Program.SchoenCycleC2DeckTransportHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothUniquenessHelpers

/-! # Exact normalized absolute classes on literal isomorphic subschemes -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Supplied normalized coclasses on a literal subscheme and its actual isomorphic pullback have exactly the corresponding absolute pullbacks. -/
theorem normalized_subscheme_absolute_iso {Q P : Over (Spec ↧ℂ)}
    [Smooth Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (e : Q ≅ P) (I : P.left.IdealSheafData)
    [IsIntegral (s2c_subscheme P I).left]
    [IsIntegral (s2c_subscheme Q (I.comap e.hom.left)).left]
    (k : ℕ)
    (hcodim : ∀ x ∈ (s2e_componentCycle
      (s2c_subschemeι Q (I.comap e.hom.left)) ℚ).support, (k : ℕ∞) ≤ Order.coheight x)
    (cQ : s2e_supportedClass Q
      (s2e_componentCycle (s2c_subschemeι Q (I.comap e.hom.left)) ℚ) k)
    (cP : s2e_supportedClass P (s2e_componentCycle (s2c_subschemeι P I) ℚ) k)
    (hcQ : a3b4_IsCycleClass Q.hom
      (s2e_componentCycle (s2c_subschemeι Q (I.comap e.hom.left)) ℚ) k cQ)
    (hcP : a3b4_IsCycleClass P.hom (s2e_componentCycle (s2c_subschemeι P I) ℚ) k cP) :
    s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q (I.comap e.hom.left)) ℚ) k cQ =
      s2e_pullback ℚ e.hom (2 * k)
        (s2e_classToAbsolute P (s2e_componentCycle (s2c_subschemeι P I) ℚ) k cP) := by
  let jQ := s2c_subschemeι Q (I.comap e.hom.left)
  let jP := s2c_subschemeι P I
  letI : IsClosedImmersion jQ.left :=
    inferInstanceAs (IsClosedImmersion (I.comap e.hom.left).subschemeι)
  letI : IsClosedImmersion (jQ ≫ e.hom).left := by
    change IsClosedImmersion (jQ.left ≫ e.hom.left)
    infer_instance
  have hf : Topology.IsOpenEmbedding (Point.map e.hom) :=
    (s2e_pointHomeomorphOfIso e).isOpenEmbedding
  have hcycle := subscheme_comap_componentCycle e I
  have hex : ∀ c : s2e_supportedClass P (s2e_componentCycle (jQ ≫ e.hom) ℚ) k,
      a3b4_IsCycleClass P.hom (s2e_componentCycle (jQ ≫ e.hom) ℚ) k c →
      ∃ b : s2e_supportedClass Q (s2e_componentCycle jQ ℚ) k,
        a3b4_IsCycleClass Q.hom (s2e_componentCycle jQ ℚ) k b ∧
        s2e_classToAbsolute Q (s2e_componentCycle jQ ℚ) k b =
          s2e_pullback ℚ e.hom (2 * k)
            (s2e_classToAbsolute P (s2e_componentCycle (jQ ≫ e.hom) ℚ) k c) := by
    intro c hc
    let b := relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap jQ e.hom) c
    refine ⟨b, ?_, s2e_componentOpenPairMap_absolute jQ e.hom k c⟩
    exact s2e_componentCycle_normalized_open_pullback jQ e.hom hf k
      (fun r E hE z => s2e_iso_holomorphicChart_forward Q P e.hom r k E hE z)
      b c hc rfl
  change s2e_componentCycle (jQ ≫ e.hom) ℚ = s2e_componentCycle jP ℚ at hcycle
  rw [hcycle] at hex
  obtain ⟨b, hb, habs⟩ := hex cP hcP
  have hbc : b = cQ := s2e_cycleClass_unique_smooth Q.hom
    (s2e_componentCycle jQ ℚ) k hcodim b cQ hb hcQ
  rw [hbc] at habs
  exact habs

#print axioms normalized_subscheme_absolute_iso
end HodgeLean.Foundations.Program.G32Native.EulerModel
