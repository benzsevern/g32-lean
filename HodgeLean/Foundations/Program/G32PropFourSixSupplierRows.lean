import HodgeLean.Foundations.Program.G32PropFourSixPacked0008
import HodgeLean.Foundations.Program.G32PropFourSixCharacters
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCharacter
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow02
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow03
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow04
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow05
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow06
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow07
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow08
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow09
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow10
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow11
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow12
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow14
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow15
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow16
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow17
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow18
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow19
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow20
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow21
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow22
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow23
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow24
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow25
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow26
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow27
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow28
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow29
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow30
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow31
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow32
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow33
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow34
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow35
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow36
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow37
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow38
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow39
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow40
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow41
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow42
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow43
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow44
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow45
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow46
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow47
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow48
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow49
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow50
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow51

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_recordedSuppliers : Fin 51 → g32p_Supplier :=
  ![g32p_determinantSupplier,
    g32p_row02_finiteSupplier,
    g32p_row03_finiteSupplier,
    g32p_row04_finiteSupplier,
    g32p_row05_finiteSupplier,
    g32p_row06_finiteSupplier,
    g32p_row07_finiteSupplier,
    g32p_row08_finiteSupplier,
    g32p_row09_finiteSupplier,
    g32p_row10_finiteSupplier,
    g32p_row11_finiteSupplier,
    g32p_row12_finiteSupplier,
    g32p_row13_finiteSupplier,
    g32p_row14_finiteSupplier,
    g32p_row15_finiteSupplier,
    g32p_row16_finiteSupplier,
    g32p_row17_finiteSupplier,
    g32p_row18_finiteSupplier,
    g32p_row19_finiteSupplier,
    g32p_row20_finiteSupplier,
    g32p_row21_finiteSupplier,
    g32p_row22_finiteSupplier,
    g32p_row23_finiteSupplier,
    g32p_row24_finiteSupplier,
    g32p_row25_finiteSupplier,
    g32p_row26_finiteSupplier,
    g32p_row27_finiteSupplier,
    g32p_row28_finiteSupplier,
    g32p_row29_finiteSupplier,
    g32p_row30_finiteSupplier,
    g32p_row31_finiteSupplier,
    g32p_row32_finiteSupplier,
    g32p_row33_finiteSupplier,
    g32p_row34_finiteSupplier,
    g32p_row35_finiteSupplier,
    g32p_row36_finiteSupplier,
    g32p_row37_finiteSupplier,
    g32p_row38_finiteSupplier,
    g32p_row39_finiteSupplier,
    g32p_row40_finiteSupplier,
    g32p_row41_finiteSupplier,
    g32p_row42_finiteSupplier,
    g32p_row43_finiteSupplier,
    g32p_row44_finiteSupplier,
    g32p_row45_finiteSupplier,
    g32p_row46_finiteSupplier,
    g32p_row47_finiteSupplier,
    g32p_row48_finiteSupplier,
    g32p_row49_finiteSupplier,
    g32p_row50_finiteSupplier,
    g32p_row51_finiteSupplier]

def g32p_recordedSupplierOrders : Fin 51 → ℕ :=
  ![155520, 3456, 4320, 1728, 486, 144, 1944, 648, 486, 486, 486, 486, 24, 24, 96, 15, 1296, 36, 1152, 144, 972, 576, 108, 1152, 576, 576, 486, 486, 486, 324, 18, 648, 432, 480, 432, 384, 144, 144, 144, 144, 54, 576, 432, 432, 486, 432, 432, 384, 324, 243, 216]

def g32p_recordedSupplierModuli : Fin 51 → ℕ :=
  ![3, 6, 6, 3, 3, 6, 3, 6, 6, 6, 6, 6, 12, 12, 12, 15, 6, 6, 6, 6, 3, 6, 3, 6, 6, 6, 3, 6, 3, 6, 6, 3, 3, 15, 3, 6, 6, 3, 6, 3, 6, 3, 6, 3, 3, 6, 3, 6, 12, 3, 3]

theorem g32p_recordedSuppliers_order (i : Fin 51) :
    Nat.card (g32p_recordedSuppliers i).H = g32p_recordedSupplierOrders i := by
  fin_cases i
  · exact g32p_determinantSupplier_order
  · exact g32p_row02_finiteSupplier_order
  · exact g32p_row03_finiteSupplier_order
  · exact g32p_row04_finiteSupplier_order
  · exact g32p_row05_finiteSupplier_order
  · exact g32p_row06_finiteSupplier_order
  · exact g32p_row07_finiteSupplier_order
  · exact g32p_row08_finiteSupplier_order
  · exact g32p_row09_finiteSupplier_order
  · exact g32p_row10_finiteSupplier_order
  · exact g32p_row11_finiteSupplier_order
  · exact g32p_row12_finiteSupplier_order
  · exact g32p_row13_finiteSupplier_order
  · exact g32p_row14_finiteSupplier_order
  · exact g32p_row15_finiteSupplier_order
  · exact g32p_row16_finiteSupplier_order
  · exact g32p_row17_finiteSupplier_order
  · exact g32p_row18_finiteSupplier_order
  · exact g32p_row19_finiteSupplier_order
  · exact g32p_row20_finiteSupplier_order
  · exact g32p_row21_finiteSupplier_order
  · exact g32p_row22_finiteSupplier_order
  · exact g32p_row23_finiteSupplier_order
  · exact g32p_row24_finiteSupplier_order
  · exact g32p_row25_finiteSupplier_order
  · exact g32p_row26_finiteSupplier_order
  · exact g32p_row27_finiteSupplier_order
  · exact g32p_row28_finiteSupplier_order
  · exact g32p_row29_finiteSupplier_order
  · exact g32p_row30_finiteSupplier_order
  · exact g32p_row31_finiteSupplier_order
  · exact g32p_row32_finiteSupplier_order
  · exact g32p_row33_finiteSupplier_order
  · exact g32p_row34_finiteSupplier_order
  · exact g32p_row35_finiteSupplier_order
  · exact g32p_row36_finiteSupplier_order
  · exact g32p_row37_finiteSupplier_order
  · exact g32p_row38_finiteSupplier_order
  · exact g32p_row39_finiteSupplier_order
  · exact g32p_row40_finiteSupplier_order
  · exact g32p_row41_finiteSupplier_order
  · exact g32p_row42_finiteSupplier_order
  · exact g32p_row43_finiteSupplier_order
  · exact g32p_row44_finiteSupplier_order
  · exact g32p_row45_finiteSupplier_order
  · exact g32p_row46_finiteSupplier_order
  · exact g32p_row47_finiteSupplier_order
  · exact g32p_row48_finiteSupplier_order
  · exact g32p_row49_finiteSupplier_order
  · exact g32p_row50_finiteSupplier_order
  · exact g32p_row51_finiteSupplier_order

theorem g32p_recordedSuppliers_modulus (i : Fin 51) :
    (g32p_recordedSuppliers i).m = g32p_recordedSupplierModuli i := by
  fin_cases i <;> rfl

theorem g32p_recordedSupplierNumbers_table : ∀ i : Fin 51,
    ∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧
      r.orderH = g32p_recordedSupplierOrders i ∧ r.m = g32p_recordedSupplierModuli i := by
  decide +kernel

theorem g32p_recordedSuppliers_table (i : Fin 51) :
    ∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧
      r.orderH = Nat.card (g32p_recordedSuppliers i).H ∧ r.m = (g32p_recordedSuppliers i).m := by
  rw [g32p_recordedSuppliers_order, g32p_recordedSuppliers_modulus]
  exact g32p_recordedSupplierNumbers_table i

def g32p_recordedSupplierCharacters (i : Fin 51) : (g32p_recordedSuppliers i).H →* ℂˣ :=
  g32p_complexCharacter (g32p_recordedSuppliers i)

theorem g32p_recordedSupplierCharacters_apply (i : Fin 51)
    (h : (g32p_recordedSuppliers i).H) :
    (g32p_recordedSupplierCharacters i h : ℂ) =
      g32p_root (g32p_recordedSuppliers i).m ^
        (Multiplicative.toAdd ((g32p_recordedSuppliers i).χ h)).val :=
  g32p_complexCharacter_apply _ _

end HodgeLean.Foundations.Program
