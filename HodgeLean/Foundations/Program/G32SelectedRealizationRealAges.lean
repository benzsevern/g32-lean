import HodgeLean.Foundations.Program.G32SelectedRealizationSupplierAges

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32y_supplier_real_residue_sum {G : Type*} [Group G] [Finite G]
    {m : ℕ} [NeZero m] (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (gs : List G) (hs : IsSimpleExps m (papersExpsList H χ gs)) (u : (ZMod m)ˣ) :
    2 * ((papersExpsList H χ gs).map fun a : ℕ ↦
      ((((u : ZMod m) * (a : ZMod m)).val : ℝ) / m)).sum =
        ((papersExpsList H χ gs).length : ℝ) := by
  have hh := congrArg (Rat.castHom ℝ) (g32y_supplier_residue_sum H χ gs hs u)
  simpa only [map_mul, map_ofNat, map_natCast, map_list_sum, List.map_map,
    Function.comp_def, Rat.coe_castHom, Rat.cast_div, Rat.cast_natCast] using hh

end HodgeLean.Foundations.Program
