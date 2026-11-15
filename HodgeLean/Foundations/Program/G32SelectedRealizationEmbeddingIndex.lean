import HodgeLean.Foundations.Program.G32PropFourSixCharacters
import HodgeLean.Foundations.Program.G32SelectedRealizationSupplierCharacter

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32y_embedding_root_index (S : g32p_Supplier)
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    ∃ u : (ZMod S.m)ˣ, σ (g32p_zeta S) = g32p_root S.m ^ (u : ZMod S.m).val := by
  have hz := IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)
  have hs : IsPrimitiveRoot (σ (g32p_zeta S)) S.m := hz.map_of_injective σ.injective
  obtain ⟨i, hi, hic, hp⟩ := (g32p_root_primitive S).isPrimitiveRoot_iff.mp hs
  refine ⟨ZMod.unitOfCoprime i hic, ?_⟩
  simpa only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi] using hp.symm

end HodgeLean.Foundations.Program
