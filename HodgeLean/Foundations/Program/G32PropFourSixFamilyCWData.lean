import HodgeLean.Foundations.Program.G32PropFourSixPacked0442

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

/-- Branch class labels in literal class order.
Source: G32 v0.16, Definition 3.5, Proposition 3.1 and Appendix A. -/
def g32p_familyCWBranchClass : Fin 13 → Fin 102 :=
  fun j => if j.val < 6 then 1 else if j.val < 12 then 2 else 18

/-- Periods of the branch elements.
Source: G32 v0.16, Definition 3.5, Proposition 3.1 and Appendix A. -/
def g32p_familyCWPeriod : Fin 13 → ℕ :=
  fun j => if j.val < 12 then 3 else 2

/-- Dimensions obtained by cyclic averaging of the recorded traces.
Source: G32 v0.16, Definition 3.5, Proposition 3.1 and Appendix A. -/
def g32p_familyCWFixed : Fin 102 → Fin 13 → ℕ :=
  fun i j => if j.val < 12 then ![1, 0, 0, 1, 1, 0, 0, 3, 3, 2, 2, 0, 0, 3, 3, 0, 3, 3, 1, 1, 6, 6, 3, 3, 9, 3, 3, 3, 6, 6, 2, 8, 8, 8, 11, 11, 9, 9, 9, 9, 3, 3, 3, 3, 6, 6, 6, 6, 12, 6, 6, 12, 9, 9, 6, 6, 15, 15, 9, 9, 9, 9, 9, 9, 18, 18, 10, 10, 12, 12, 18, 18, 18, 18, 9, 9, 18, 18, 18, 24, 21, 21, 21, 21, 24, 24, 15, 15, 18, 18, 16, 16, 24, 24, 24, 24, 32, 24, 24, 27, 27, 27] i else ![1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 6, 6, 6, 6, 6, 7, 11, 7, 7, 11, 11, 10, 12, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 16, 16, 16, 10, 18, 18, 18, 18, 18, 18, 10, 10, 18, 18, 18, 18, 18, 18, 16, 16, 16, 16, 16, 16, 21, 21, 21, 21, 21, 21, 30, 28, 30, 30, 30, 30, 30, 30, 30, 30, 28, 28, 32, 32, 32, 32, 32, 32, 40, 40, 40, 45, 45, 45] i

/-- Dimensions of the character rows.
Source: G32 v0.16, Definition 3.5, Proposition 3.1 and Appendix A. -/
def g32p_familyCWDimension : Fin 102 → ℕ :=
  ![1, 1, 1, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 10, 10, 10, 10, 10, 10, 15, 15, 15, 15, 15, 15, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 30, 30, 30, 30, 30, 30, 30, 30, 30, 36, 36, 36, 36, 36, 36, 40, 40, 40, 40, 40, 40, 45, 45, 45, 45, 45, 45, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 64, 64, 64, 64, 64, 64, 80, 80, 80, 81, 81, 81]

/-- CW multiplicities computed from the thirteen branch dimensions.
Source: G32 v0.16, Definition 3.5, Proposition 3.1 and Appendix A. -/
def g32p_familyCWMultiplicity : Fin 102 → ℤ :=
  ![-2, 10, 10, 30, 30, 42, 42, 6, 6, 30, 30, 54, 54, 18, 18, 64, 28, 28, 92, 92, 32, 32, 68, 68, 50, 118, 122, 122, 82, 82, 186, 112, 114, 114, 78, 78, 102, 102, 102, 102, 174, 174, 174, 174, 138, 138, 136, 136, 104, 176, 176, 176, 204, 204, 240, 240, 132, 132, 212, 212, 270, 270, 270, 270, 162, 162, 304, 304, 280, 280, 208, 208, 258, 258, 366, 366, 258, 258, 414, 344, 378, 378, 378, 378, 342, 342, 450, 450, 416, 416, 480, 480, 384, 384, 384, 384, 456, 552, 552, 522, 522, 522]


end HodgeLean.Foundations.Program
