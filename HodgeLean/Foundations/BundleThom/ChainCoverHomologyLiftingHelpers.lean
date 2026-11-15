import HodgeLean.Foundations.BundleThom.ChainDualPullbackHelpers
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Homology lifting along degreewise monic chain covers

A lift of a cycle is a cycle because the outgoing chain map is monic.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- A family of degreewise monic chain maps covering projective maps in one chain degree also covers projective maps to homology in that degree.
Source: Hatcher, Algebraic Topology, §2.1, cycle representatives in directed chain unions. -/
theorem i1_chainCover_projectiveHomology_factor {ι : Type}
    (K : ChainComplex (ModuleCat ℚ) ℕ) (L : ι → ChainComplex (ModuleCat ℚ) ℕ)
    (p : ∀ i, L i ⟶ K) [∀ i j, Mono ((p i).f j)]
    (A : ModuleCat ℚ) [Projective A] (n : ℕ)
    (hcover : ∀ f : A ⟶ K.X n, ∃ i, ∃ g : A ⟶ (L i).X n, g ≫ (p i).f n = f)
    (f : A ⟶ K.homology n) :
    ∃ i, ∃ g : A ⟶ (L i).homology n, g ≫ HomologicalComplex.homologyMap (p i) n = f := by
  let c := Projective.factorThru f (K.homologyπ n)
  obtain ⟨i, g, hg⟩ := hcover (c ≫ K.iCycles n)
  have hz : g ≫ (L i).d n ((ComplexShape.down ℕ).next n) = 0 := by
    apply (cancel_mono ((p i).f ((ComplexShape.down ℕ).next n))).mp
    rw [zero_comp, Category.assoc, ← (p i).comm, ← Category.assoc, hg,
      Category.assoc, K.iCycles_d, comp_zero]
  let d := (L i).liftCycles g ((ComplexShape.down ℕ).next n) rfl hz
  have hd : d ≫ HomologicalComplex.cyclesMap (p i) n = c := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      HomologicalComplex.liftCycles_i]
    exact hg
  refine ⟨i, d ≫ (L i).homologyπ n, ?_⟩
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hd]
  exact Projective.factorThru_comp f (K.homologyπ n)

end HodgeLean.Foundations.BundleThom
