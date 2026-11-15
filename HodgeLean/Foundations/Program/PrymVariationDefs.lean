import HodgeLean.Foundations.Program.PrymFamilyB4Defs

/-! # B6-3a: slots in the printed root tuple

These finite index maps retain the order of the root in `PrymFamilyB4Defs`.
They carry no geometric family data. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The six positions occupied by the first reflection class.
Source: `b4b_root`; G32 v0.16, Definition 3.5 and Appendix A. -/
def b63_positiveSlot : Fin 6 → Fin 13 := ![0, 2, 4, 6, 8, 10]

example : b63_positiveSlot 1 = 2 := rfl

/-- The six positions occupied by the inverse reflection class.
Source: `b4b_root`; G32 v0.16, Definition 3.5 and Appendix A. -/
def b63_negativeSlot : Fin 6 → Fin 13 := ![1, 3, 5, 7, 9, 11]

example : b63_negativeSlot 5 = 11 := rfl

end HodgeLean.Foundations.Program
