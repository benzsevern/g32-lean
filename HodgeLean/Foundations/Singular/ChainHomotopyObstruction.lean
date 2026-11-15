import HodgeLean.Foundations.Singular.ProductChains

/-! The cycle obstruction for extending an actual rational chain homotopy. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Cycle control in one degree makes the next chain-homotopy obstruction a cycle.
Source: Hatcher, Algebraic Topology, §2.1, chain homotopies and the acyclic-models induction. -/
theorem chainHomotopy_obstruction_cycle
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f g : K ⟶ L) (n : ℕ)
    (h : K.X n →ₗ[ℚ] L.X (n + 1))
    (hh : ∀ z : K.X n, (K.d n (n - 1)).hom z = 0 →
      (L.d (n + 1) n).hom (h z) = (f.f n).hom z - (g.f n).hom z)
    (z : K.X (n + 1)) :
    (L.d (n + 1) n).hom
      ((f.f (n + 1)).hom z - (g.f (n + 1)).hom z - h ((K.d (n + 1) n).hom z)) = 0 := by
  have hd := congrArg (fun k => ModuleCat.Hom.hom k z) (K.d_comp_d (n + 1) n (n - 1))
  change (K.d n (n - 1)).hom ((K.d (n + 1) n).hom z) = 0 at hd
  have hf := congrArg (fun k => ModuleCat.Hom.hom k z) (f.comm (n + 1) n)
  have hg := congrArg (fun k => ModuleCat.Hom.hom k z) (g.comm (n + 1) n)
  change (L.d (n + 1) n).hom ((f.f (n + 1)).hom z) =
    (f.f n).hom ((K.d (n + 1) n).hom z) at hf
  change (L.d (n + 1) n).hom ((g.f (n + 1)).hom z) =
    (g.f n).hom ((K.d (n + 1) n).hom z) at hg
  rw [map_sub, map_sub, hf, hg, hh _ hd, sub_self]

#print axioms chainHomotopy_obstruction_cycle
end HodgeLean.Foundations.Singular
