import HodgeLean.Foundations.Program.G32PropFourSixFamilyCWData

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_000 :
    (g32p_literalCharacterValue 0 0).re = g32p_familyCWDimension 0 ∧
    (g32p_literalCharacterValue 0 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 0
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 0
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 0 j =
        g32p_familyCWDimension 0 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 0 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 0 : ℤ) -
        g32p_familyCWFixed 0 j)) = g32p_familyCWMultiplicity 0 := by
  decide +kernel

theorem g32p_familyCW_certificate_001 :
    (g32p_literalCharacterValue 1 0).re = g32p_familyCWDimension 1 ∧
    (g32p_literalCharacterValue 1 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 1
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 1
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 1 j =
        g32p_familyCWDimension 1 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 1 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 1 : ℤ) -
        g32p_familyCWFixed 1 j)) = g32p_familyCWMultiplicity 1 := by
  decide +kernel

theorem g32p_familyCW_certificate_002 :
    (g32p_literalCharacterValue 2 0).re = g32p_familyCWDimension 2 ∧
    (g32p_literalCharacterValue 2 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 2
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 2
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 2 j =
        g32p_familyCWDimension 2 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 2 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 2 : ℤ) -
        g32p_familyCWFixed 2 j)) = g32p_familyCWMultiplicity 2 := by
  decide +kernel

theorem g32p_familyCW_certificate_003 :
    (g32p_literalCharacterValue 3 0).re = g32p_familyCWDimension 3 ∧
    (g32p_literalCharacterValue 3 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 3
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 3
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 3 j =
        g32p_familyCWDimension 3 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 3 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 3 : ℤ) -
        g32p_familyCWFixed 3 j)) = g32p_familyCWMultiplicity 3 := by
  decide +kernel

theorem g32p_familyCW_certificate_004 :
    (g32p_literalCharacterValue 4 0).re = g32p_familyCWDimension 4 ∧
    (g32p_literalCharacterValue 4 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 4
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 4
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 4 j =
        g32p_familyCWDimension 4 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 4 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 4 : ℤ) -
        g32p_familyCWFixed 4 j)) = g32p_familyCWMultiplicity 4 := by
  decide +kernel

theorem g32p_familyCW_certificate_005 :
    (g32p_literalCharacterValue 5 0).re = g32p_familyCWDimension 5 ∧
    (g32p_literalCharacterValue 5 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 5
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 5
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 5 j =
        g32p_familyCWDimension 5 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 5 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 5 : ℤ) -
        g32p_familyCWFixed 5 j)) = g32p_familyCWMultiplicity 5 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_006 :
    (g32p_literalCharacterValue 6 0).re = g32p_familyCWDimension 6 ∧
    (g32p_literalCharacterValue 6 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 6
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 6
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 6 j =
        g32p_familyCWDimension 6 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 6 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 6 : ℤ) -
        g32p_familyCWFixed 6 j)) = g32p_familyCWMultiplicity 6 := by
  decide +kernel

theorem g32p_familyCW_certificate_007 :
    (g32p_literalCharacterValue 7 0).re = g32p_familyCWDimension 7 ∧
    (g32p_literalCharacterValue 7 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 7
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 7
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 7 j =
        g32p_familyCWDimension 7 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 7 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 7 : ℤ) -
        g32p_familyCWFixed 7 j)) = g32p_familyCWMultiplicity 7 := by
  decide +kernel

theorem g32p_familyCW_certificate_008 :
    (g32p_literalCharacterValue 8 0).re = g32p_familyCWDimension 8 ∧
    (g32p_literalCharacterValue 8 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 8
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 8
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 8 j =
        g32p_familyCWDimension 8 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 8 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 8 : ℤ) -
        g32p_familyCWFixed 8 j)) = g32p_familyCWMultiplicity 8 := by
  decide +kernel

theorem g32p_familyCW_certificate_009 :
    (g32p_literalCharacterValue 9 0).re = g32p_familyCWDimension 9 ∧
    (g32p_literalCharacterValue 9 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 9
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 9
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 9 j =
        g32p_familyCWDimension 9 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 9 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 9 : ℤ) -
        g32p_familyCWFixed 9 j)) = g32p_familyCWMultiplicity 9 := by
  decide +kernel

theorem g32p_familyCW_certificate_010 :
    (g32p_literalCharacterValue 10 0).re = g32p_familyCWDimension 10 ∧
    (g32p_literalCharacterValue 10 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 10
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 10
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 10 j =
        g32p_familyCWDimension 10 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 10 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 10 : ℤ) -
        g32p_familyCWFixed 10 j)) = g32p_familyCWMultiplicity 10 := by
  decide +kernel

theorem g32p_familyCW_certificate_011 :
    (g32p_literalCharacterValue 11 0).re = g32p_familyCWDimension 11 ∧
    (g32p_literalCharacterValue 11 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 11
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 11
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 11 j =
        g32p_familyCWDimension 11 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 11 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 11 : ℤ) -
        g32p_familyCWFixed 11 j)) = g32p_familyCWMultiplicity 11 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_012 :
    (g32p_literalCharacterValue 12 0).re = g32p_familyCWDimension 12 ∧
    (g32p_literalCharacterValue 12 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 12
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 12
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 12 j =
        g32p_familyCWDimension 12 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 12 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 12 : ℤ) -
        g32p_familyCWFixed 12 j)) = g32p_familyCWMultiplicity 12 := by
  decide +kernel

theorem g32p_familyCW_certificate_013 :
    (g32p_literalCharacterValue 13 0).re = g32p_familyCWDimension 13 ∧
    (g32p_literalCharacterValue 13 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 13
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 13
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 13 j =
        g32p_familyCWDimension 13 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 13 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 13 : ℤ) -
        g32p_familyCWFixed 13 j)) = g32p_familyCWMultiplicity 13 := by
  decide +kernel

theorem g32p_familyCW_certificate_014 :
    (g32p_literalCharacterValue 14 0).re = g32p_familyCWDimension 14 ∧
    (g32p_literalCharacterValue 14 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 14
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 14
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 14 j =
        g32p_familyCWDimension 14 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 14 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 14 : ℤ) -
        g32p_familyCWFixed 14 j)) = g32p_familyCWMultiplicity 14 := by
  decide +kernel

theorem g32p_familyCW_certificate_015 :
    (g32p_literalCharacterValue 15 0).re = g32p_familyCWDimension 15 ∧
    (g32p_literalCharacterValue 15 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 15
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 15
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 15 j =
        g32p_familyCWDimension 15 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 15 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 15 : ℤ) -
        g32p_familyCWFixed 15 j)) = g32p_familyCWMultiplicity 15 := by
  decide +kernel

theorem g32p_familyCW_certificate_016 :
    (g32p_literalCharacterValue 16 0).re = g32p_familyCWDimension 16 ∧
    (g32p_literalCharacterValue 16 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 16
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 16
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 16 j =
        g32p_familyCWDimension 16 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 16 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 16 : ℤ) -
        g32p_familyCWFixed 16 j)) = g32p_familyCWMultiplicity 16 := by
  decide +kernel

theorem g32p_familyCW_certificate_017 :
    (g32p_literalCharacterValue 17 0).re = g32p_familyCWDimension 17 ∧
    (g32p_literalCharacterValue 17 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 17
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 17
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 17 j =
        g32p_familyCWDimension 17 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 17 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 17 : ℤ) -
        g32p_familyCWFixed 17 j)) = g32p_familyCWMultiplicity 17 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_018 :
    (g32p_literalCharacterValue 18 0).re = g32p_familyCWDimension 18 ∧
    (g32p_literalCharacterValue 18 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 18
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 18
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 18 j =
        g32p_familyCWDimension 18 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 18 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 18 : ℤ) -
        g32p_familyCWFixed 18 j)) = g32p_familyCWMultiplicity 18 := by
  decide +kernel

theorem g32p_familyCW_certificate_019 :
    (g32p_literalCharacterValue 19 0).re = g32p_familyCWDimension 19 ∧
    (g32p_literalCharacterValue 19 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 19
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 19
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 19 j =
        g32p_familyCWDimension 19 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 19 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 19 : ℤ) -
        g32p_familyCWFixed 19 j)) = g32p_familyCWMultiplicity 19 := by
  decide +kernel

theorem g32p_familyCW_certificate_020 :
    (g32p_literalCharacterValue 20 0).re = g32p_familyCWDimension 20 ∧
    (g32p_literalCharacterValue 20 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 20
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 20
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 20 j =
        g32p_familyCWDimension 20 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 20 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 20 : ℤ) -
        g32p_familyCWFixed 20 j)) = g32p_familyCWMultiplicity 20 := by
  decide +kernel

theorem g32p_familyCW_certificate_021 :
    (g32p_literalCharacterValue 21 0).re = g32p_familyCWDimension 21 ∧
    (g32p_literalCharacterValue 21 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 21
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 21
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 21 j =
        g32p_familyCWDimension 21 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 21 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 21 : ℤ) -
        g32p_familyCWFixed 21 j)) = g32p_familyCWMultiplicity 21 := by
  decide +kernel

theorem g32p_familyCW_certificate_022 :
    (g32p_literalCharacterValue 22 0).re = g32p_familyCWDimension 22 ∧
    (g32p_literalCharacterValue 22 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 22
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 22
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 22 j =
        g32p_familyCWDimension 22 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 22 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 22 : ℤ) -
        g32p_familyCWFixed 22 j)) = g32p_familyCWMultiplicity 22 := by
  decide +kernel

theorem g32p_familyCW_certificate_023 :
    (g32p_literalCharacterValue 23 0).re = g32p_familyCWDimension 23 ∧
    (g32p_literalCharacterValue 23 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 23
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 23
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 23 j =
        g32p_familyCWDimension 23 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 23 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 23 : ℤ) -
        g32p_familyCWFixed 23 j)) = g32p_familyCWMultiplicity 23 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_024 :
    (g32p_literalCharacterValue 24 0).re = g32p_familyCWDimension 24 ∧
    (g32p_literalCharacterValue 24 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 24
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 24
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 24 j =
        g32p_familyCWDimension 24 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 24 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 24 : ℤ) -
        g32p_familyCWFixed 24 j)) = g32p_familyCWMultiplicity 24 := by
  decide +kernel

theorem g32p_familyCW_certificate_025 :
    (g32p_literalCharacterValue 25 0).re = g32p_familyCWDimension 25 ∧
    (g32p_literalCharacterValue 25 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 25
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 25
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 25 j =
        g32p_familyCWDimension 25 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 25 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 25 : ℤ) -
        g32p_familyCWFixed 25 j)) = g32p_familyCWMultiplicity 25 := by
  decide +kernel

theorem g32p_familyCW_certificate_026 :
    (g32p_literalCharacterValue 26 0).re = g32p_familyCWDimension 26 ∧
    (g32p_literalCharacterValue 26 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 26
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 26
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 26 j =
        g32p_familyCWDimension 26 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 26 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 26 : ℤ) -
        g32p_familyCWFixed 26 j)) = g32p_familyCWMultiplicity 26 := by
  decide +kernel

theorem g32p_familyCW_certificate_027 :
    (g32p_literalCharacterValue 27 0).re = g32p_familyCWDimension 27 ∧
    (g32p_literalCharacterValue 27 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 27
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 27
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 27 j =
        g32p_familyCWDimension 27 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 27 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 27 : ℤ) -
        g32p_familyCWFixed 27 j)) = g32p_familyCWMultiplicity 27 := by
  decide +kernel

theorem g32p_familyCW_certificate_028 :
    (g32p_literalCharacterValue 28 0).re = g32p_familyCWDimension 28 ∧
    (g32p_literalCharacterValue 28 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 28
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 28
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 28 j =
        g32p_familyCWDimension 28 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 28 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 28 : ℤ) -
        g32p_familyCWFixed 28 j)) = g32p_familyCWMultiplicity 28 := by
  decide +kernel

theorem g32p_familyCW_certificate_029 :
    (g32p_literalCharacterValue 29 0).re = g32p_familyCWDimension 29 ∧
    (g32p_literalCharacterValue 29 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 29
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 29
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 29 j =
        g32p_familyCWDimension 29 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 29 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 29 : ℤ) -
        g32p_familyCWFixed 29 j)) = g32p_familyCWMultiplicity 29 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_030 :
    (g32p_literalCharacterValue 30 0).re = g32p_familyCWDimension 30 ∧
    (g32p_literalCharacterValue 30 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 30
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 30
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 30 j =
        g32p_familyCWDimension 30 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 30 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 30 : ℤ) -
        g32p_familyCWFixed 30 j)) = g32p_familyCWMultiplicity 30 := by
  decide +kernel

theorem g32p_familyCW_certificate_031 :
    (g32p_literalCharacterValue 31 0).re = g32p_familyCWDimension 31 ∧
    (g32p_literalCharacterValue 31 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 31
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 31
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 31 j =
        g32p_familyCWDimension 31 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 31 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 31 : ℤ) -
        g32p_familyCWFixed 31 j)) = g32p_familyCWMultiplicity 31 := by
  decide +kernel

theorem g32p_familyCW_certificate_032 :
    (g32p_literalCharacterValue 32 0).re = g32p_familyCWDimension 32 ∧
    (g32p_literalCharacterValue 32 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 32
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 32
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 32 j =
        g32p_familyCWDimension 32 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 32 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 32 : ℤ) -
        g32p_familyCWFixed 32 j)) = g32p_familyCWMultiplicity 32 := by
  decide +kernel

theorem g32p_familyCW_certificate_033 :
    (g32p_literalCharacterValue 33 0).re = g32p_familyCWDimension 33 ∧
    (g32p_literalCharacterValue 33 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 33
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 33
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 33 j =
        g32p_familyCWDimension 33 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 33 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 33 : ℤ) -
        g32p_familyCWFixed 33 j)) = g32p_familyCWMultiplicity 33 := by
  decide +kernel

theorem g32p_familyCW_certificate_034 :
    (g32p_literalCharacterValue 34 0).re = g32p_familyCWDimension 34 ∧
    (g32p_literalCharacterValue 34 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 34
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 34
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 34 j =
        g32p_familyCWDimension 34 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 34 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 34 : ℤ) -
        g32p_familyCWFixed 34 j)) = g32p_familyCWMultiplicity 34 := by
  decide +kernel

theorem g32p_familyCW_certificate_035 :
    (g32p_literalCharacterValue 35 0).re = g32p_familyCWDimension 35 ∧
    (g32p_literalCharacterValue 35 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 35
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 35
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 35 j =
        g32p_familyCWDimension 35 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 35 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 35 : ℤ) -
        g32p_familyCWFixed 35 j)) = g32p_familyCWMultiplicity 35 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_036 :
    (g32p_literalCharacterValue 36 0).re = g32p_familyCWDimension 36 ∧
    (g32p_literalCharacterValue 36 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 36
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 36
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 36 j =
        g32p_familyCWDimension 36 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 36 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 36 : ℤ) -
        g32p_familyCWFixed 36 j)) = g32p_familyCWMultiplicity 36 := by
  decide +kernel

theorem g32p_familyCW_certificate_037 :
    (g32p_literalCharacterValue 37 0).re = g32p_familyCWDimension 37 ∧
    (g32p_literalCharacterValue 37 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 37
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 37
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 37 j =
        g32p_familyCWDimension 37 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 37 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 37 : ℤ) -
        g32p_familyCWFixed 37 j)) = g32p_familyCWMultiplicity 37 := by
  decide +kernel

theorem g32p_familyCW_certificate_038 :
    (g32p_literalCharacterValue 38 0).re = g32p_familyCWDimension 38 ∧
    (g32p_literalCharacterValue 38 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 38
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 38
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 38 j =
        g32p_familyCWDimension 38 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 38 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 38 : ℤ) -
        g32p_familyCWFixed 38 j)) = g32p_familyCWMultiplicity 38 := by
  decide +kernel

theorem g32p_familyCW_certificate_039 :
    (g32p_literalCharacterValue 39 0).re = g32p_familyCWDimension 39 ∧
    (g32p_literalCharacterValue 39 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 39
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 39
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 39 j =
        g32p_familyCWDimension 39 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 39 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 39 : ℤ) -
        g32p_familyCWFixed 39 j)) = g32p_familyCWMultiplicity 39 := by
  decide +kernel

theorem g32p_familyCW_certificate_040 :
    (g32p_literalCharacterValue 40 0).re = g32p_familyCWDimension 40 ∧
    (g32p_literalCharacterValue 40 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 40
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 40
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 40 j =
        g32p_familyCWDimension 40 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 40 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 40 : ℤ) -
        g32p_familyCWFixed 40 j)) = g32p_familyCWMultiplicity 40 := by
  decide +kernel

theorem g32p_familyCW_certificate_041 :
    (g32p_literalCharacterValue 41 0).re = g32p_familyCWDimension 41 ∧
    (g32p_literalCharacterValue 41 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 41
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 41
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 41 j =
        g32p_familyCWDimension 41 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 41 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 41 : ℤ) -
        g32p_familyCWFixed 41 j)) = g32p_familyCWMultiplicity 41 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_042 :
    (g32p_literalCharacterValue 42 0).re = g32p_familyCWDimension 42 ∧
    (g32p_literalCharacterValue 42 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 42
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 42
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 42 j =
        g32p_familyCWDimension 42 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 42 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 42 : ℤ) -
        g32p_familyCWFixed 42 j)) = g32p_familyCWMultiplicity 42 := by
  decide +kernel

theorem g32p_familyCW_certificate_043 :
    (g32p_literalCharacterValue 43 0).re = g32p_familyCWDimension 43 ∧
    (g32p_literalCharacterValue 43 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 43
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 43
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 43 j =
        g32p_familyCWDimension 43 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 43 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 43 : ℤ) -
        g32p_familyCWFixed 43 j)) = g32p_familyCWMultiplicity 43 := by
  decide +kernel

theorem g32p_familyCW_certificate_044 :
    (g32p_literalCharacterValue 44 0).re = g32p_familyCWDimension 44 ∧
    (g32p_literalCharacterValue 44 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 44
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 44
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 44 j =
        g32p_familyCWDimension 44 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 44 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 44 : ℤ) -
        g32p_familyCWFixed 44 j)) = g32p_familyCWMultiplicity 44 := by
  decide +kernel

theorem g32p_familyCW_certificate_045 :
    (g32p_literalCharacterValue 45 0).re = g32p_familyCWDimension 45 ∧
    (g32p_literalCharacterValue 45 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 45
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 45
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 45 j =
        g32p_familyCWDimension 45 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 45 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 45 : ℤ) -
        g32p_familyCWFixed 45 j)) = g32p_familyCWMultiplicity 45 := by
  decide +kernel

theorem g32p_familyCW_certificate_046 :
    (g32p_literalCharacterValue 46 0).re = g32p_familyCWDimension 46 ∧
    (g32p_literalCharacterValue 46 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 46
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 46
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 46 j =
        g32p_familyCWDimension 46 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 46 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 46 : ℤ) -
        g32p_familyCWFixed 46 j)) = g32p_familyCWMultiplicity 46 := by
  decide +kernel

theorem g32p_familyCW_certificate_047 :
    (g32p_literalCharacterValue 47 0).re = g32p_familyCWDimension 47 ∧
    (g32p_literalCharacterValue 47 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 47
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 47
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 47 j =
        g32p_familyCWDimension 47 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 47 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 47 : ℤ) -
        g32p_familyCWFixed 47 j)) = g32p_familyCWMultiplicity 47 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_048 :
    (g32p_literalCharacterValue 48 0).re = g32p_familyCWDimension 48 ∧
    (g32p_literalCharacterValue 48 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 48
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 48
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 48 j =
        g32p_familyCWDimension 48 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 48 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 48 : ℤ) -
        g32p_familyCWFixed 48 j)) = g32p_familyCWMultiplicity 48 := by
  decide +kernel

theorem g32p_familyCW_certificate_049 :
    (g32p_literalCharacterValue 49 0).re = g32p_familyCWDimension 49 ∧
    (g32p_literalCharacterValue 49 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 49
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 49
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 49 j =
        g32p_familyCWDimension 49 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 49 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 49 : ℤ) -
        g32p_familyCWFixed 49 j)) = g32p_familyCWMultiplicity 49 := by
  decide +kernel

theorem g32p_familyCW_certificate_050 :
    (g32p_literalCharacterValue 50 0).re = g32p_familyCWDimension 50 ∧
    (g32p_literalCharacterValue 50 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 50
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 50
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 50 j =
        g32p_familyCWDimension 50 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 50 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 50 : ℤ) -
        g32p_familyCWFixed 50 j)) = g32p_familyCWMultiplicity 50 := by
  decide +kernel

theorem g32p_familyCW_certificate_051 :
    (g32p_literalCharacterValue 51 0).re = g32p_familyCWDimension 51 ∧
    (g32p_literalCharacterValue 51 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 51
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 51
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 51 j =
        g32p_familyCWDimension 51 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 51 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 51 : ℤ) -
        g32p_familyCWFixed 51 j)) = g32p_familyCWMultiplicity 51 := by
  decide +kernel

theorem g32p_familyCW_certificate_052 :
    (g32p_literalCharacterValue 52 0).re = g32p_familyCWDimension 52 ∧
    (g32p_literalCharacterValue 52 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 52
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 52
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 52 j =
        g32p_familyCWDimension 52 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 52 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 52 : ℤ) -
        g32p_familyCWFixed 52 j)) = g32p_familyCWMultiplicity 52 := by
  decide +kernel

theorem g32p_familyCW_certificate_053 :
    (g32p_literalCharacterValue 53 0).re = g32p_familyCWDimension 53 ∧
    (g32p_literalCharacterValue 53 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 53
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 53
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 53 j =
        g32p_familyCWDimension 53 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 53 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 53 : ℤ) -
        g32p_familyCWFixed 53 j)) = g32p_familyCWMultiplicity 53 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_054 :
    (g32p_literalCharacterValue 54 0).re = g32p_familyCWDimension 54 ∧
    (g32p_literalCharacterValue 54 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 54
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 54
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 54 j =
        g32p_familyCWDimension 54 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 54 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 54 : ℤ) -
        g32p_familyCWFixed 54 j)) = g32p_familyCWMultiplicity 54 := by
  decide +kernel

theorem g32p_familyCW_certificate_055 :
    (g32p_literalCharacterValue 55 0).re = g32p_familyCWDimension 55 ∧
    (g32p_literalCharacterValue 55 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 55
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 55
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 55 j =
        g32p_familyCWDimension 55 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 55 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 55 : ℤ) -
        g32p_familyCWFixed 55 j)) = g32p_familyCWMultiplicity 55 := by
  decide +kernel

theorem g32p_familyCW_certificate_056 :
    (g32p_literalCharacterValue 56 0).re = g32p_familyCWDimension 56 ∧
    (g32p_literalCharacterValue 56 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 56
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 56
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 56 j =
        g32p_familyCWDimension 56 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 56 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 56 : ℤ) -
        g32p_familyCWFixed 56 j)) = g32p_familyCWMultiplicity 56 := by
  decide +kernel

theorem g32p_familyCW_certificate_057 :
    (g32p_literalCharacterValue 57 0).re = g32p_familyCWDimension 57 ∧
    (g32p_literalCharacterValue 57 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 57
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 57
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 57 j =
        g32p_familyCWDimension 57 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 57 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 57 : ℤ) -
        g32p_familyCWFixed 57 j)) = g32p_familyCWMultiplicity 57 := by
  decide +kernel

theorem g32p_familyCW_certificate_058 :
    (g32p_literalCharacterValue 58 0).re = g32p_familyCWDimension 58 ∧
    (g32p_literalCharacterValue 58 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 58
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 58
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 58 j =
        g32p_familyCWDimension 58 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 58 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 58 : ℤ) -
        g32p_familyCWFixed 58 j)) = g32p_familyCWMultiplicity 58 := by
  decide +kernel

theorem g32p_familyCW_certificate_059 :
    (g32p_literalCharacterValue 59 0).re = g32p_familyCWDimension 59 ∧
    (g32p_literalCharacterValue 59 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 59
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 59
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 59 j =
        g32p_familyCWDimension 59 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 59 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 59 : ℤ) -
        g32p_familyCWFixed 59 j)) = g32p_familyCWMultiplicity 59 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_060 :
    (g32p_literalCharacterValue 60 0).re = g32p_familyCWDimension 60 ∧
    (g32p_literalCharacterValue 60 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 60
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 60
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 60 j =
        g32p_familyCWDimension 60 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 60 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 60 : ℤ) -
        g32p_familyCWFixed 60 j)) = g32p_familyCWMultiplicity 60 := by
  decide +kernel

theorem g32p_familyCW_certificate_061 :
    (g32p_literalCharacterValue 61 0).re = g32p_familyCWDimension 61 ∧
    (g32p_literalCharacterValue 61 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 61
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 61
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 61 j =
        g32p_familyCWDimension 61 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 61 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 61 : ℤ) -
        g32p_familyCWFixed 61 j)) = g32p_familyCWMultiplicity 61 := by
  decide +kernel

theorem g32p_familyCW_certificate_062 :
    (g32p_literalCharacterValue 62 0).re = g32p_familyCWDimension 62 ∧
    (g32p_literalCharacterValue 62 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 62
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 62
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 62 j =
        g32p_familyCWDimension 62 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 62 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 62 : ℤ) -
        g32p_familyCWFixed 62 j)) = g32p_familyCWMultiplicity 62 := by
  decide +kernel

theorem g32p_familyCW_certificate_063 :
    (g32p_literalCharacterValue 63 0).re = g32p_familyCWDimension 63 ∧
    (g32p_literalCharacterValue 63 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 63
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 63
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 63 j =
        g32p_familyCWDimension 63 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 63 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 63 : ℤ) -
        g32p_familyCWFixed 63 j)) = g32p_familyCWMultiplicity 63 := by
  decide +kernel

theorem g32p_familyCW_certificate_064 :
    (g32p_literalCharacterValue 64 0).re = g32p_familyCWDimension 64 ∧
    (g32p_literalCharacterValue 64 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 64
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 64
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 64 j =
        g32p_familyCWDimension 64 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 64 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 64 : ℤ) -
        g32p_familyCWFixed 64 j)) = g32p_familyCWMultiplicity 64 := by
  decide +kernel

theorem g32p_familyCW_certificate_065 :
    (g32p_literalCharacterValue 65 0).re = g32p_familyCWDimension 65 ∧
    (g32p_literalCharacterValue 65 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 65
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 65
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 65 j =
        g32p_familyCWDimension 65 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 65 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 65 : ℤ) -
        g32p_familyCWFixed 65 j)) = g32p_familyCWMultiplicity 65 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_066 :
    (g32p_literalCharacterValue 66 0).re = g32p_familyCWDimension 66 ∧
    (g32p_literalCharacterValue 66 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 66
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 66
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 66 j =
        g32p_familyCWDimension 66 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 66 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 66 : ℤ) -
        g32p_familyCWFixed 66 j)) = g32p_familyCWMultiplicity 66 := by
  decide +kernel

theorem g32p_familyCW_certificate_067 :
    (g32p_literalCharacterValue 67 0).re = g32p_familyCWDimension 67 ∧
    (g32p_literalCharacterValue 67 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 67
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 67
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 67 j =
        g32p_familyCWDimension 67 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 67 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 67 : ℤ) -
        g32p_familyCWFixed 67 j)) = g32p_familyCWMultiplicity 67 := by
  decide +kernel

theorem g32p_familyCW_certificate_068 :
    (g32p_literalCharacterValue 68 0).re = g32p_familyCWDimension 68 ∧
    (g32p_literalCharacterValue 68 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 68
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 68
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 68 j =
        g32p_familyCWDimension 68 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 68 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 68 : ℤ) -
        g32p_familyCWFixed 68 j)) = g32p_familyCWMultiplicity 68 := by
  decide +kernel

theorem g32p_familyCW_certificate_069 :
    (g32p_literalCharacterValue 69 0).re = g32p_familyCWDimension 69 ∧
    (g32p_literalCharacterValue 69 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 69
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 69
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 69 j =
        g32p_familyCWDimension 69 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 69 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 69 : ℤ) -
        g32p_familyCWFixed 69 j)) = g32p_familyCWMultiplicity 69 := by
  decide +kernel

theorem g32p_familyCW_certificate_070 :
    (g32p_literalCharacterValue 70 0).re = g32p_familyCWDimension 70 ∧
    (g32p_literalCharacterValue 70 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 70
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 70
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 70 j =
        g32p_familyCWDimension 70 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 70 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 70 : ℤ) -
        g32p_familyCWFixed 70 j)) = g32p_familyCWMultiplicity 70 := by
  decide +kernel

theorem g32p_familyCW_certificate_071 :
    (g32p_literalCharacterValue 71 0).re = g32p_familyCWDimension 71 ∧
    (g32p_literalCharacterValue 71 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 71
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 71
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 71 j =
        g32p_familyCWDimension 71 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 71 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 71 : ℤ) -
        g32p_familyCWFixed 71 j)) = g32p_familyCWMultiplicity 71 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_072 :
    (g32p_literalCharacterValue 72 0).re = g32p_familyCWDimension 72 ∧
    (g32p_literalCharacterValue 72 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 72
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 72
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 72 j =
        g32p_familyCWDimension 72 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 72 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 72 : ℤ) -
        g32p_familyCWFixed 72 j)) = g32p_familyCWMultiplicity 72 := by
  decide +kernel

theorem g32p_familyCW_certificate_073 :
    (g32p_literalCharacterValue 73 0).re = g32p_familyCWDimension 73 ∧
    (g32p_literalCharacterValue 73 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 73
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 73
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 73 j =
        g32p_familyCWDimension 73 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 73 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 73 : ℤ) -
        g32p_familyCWFixed 73 j)) = g32p_familyCWMultiplicity 73 := by
  decide +kernel

theorem g32p_familyCW_certificate_074 :
    (g32p_literalCharacterValue 74 0).re = g32p_familyCWDimension 74 ∧
    (g32p_literalCharacterValue 74 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 74
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 74
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 74 j =
        g32p_familyCWDimension 74 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 74 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 74 : ℤ) -
        g32p_familyCWFixed 74 j)) = g32p_familyCWMultiplicity 74 := by
  decide +kernel

theorem g32p_familyCW_certificate_075 :
    (g32p_literalCharacterValue 75 0).re = g32p_familyCWDimension 75 ∧
    (g32p_literalCharacterValue 75 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 75
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 75
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 75 j =
        g32p_familyCWDimension 75 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 75 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 75 : ℤ) -
        g32p_familyCWFixed 75 j)) = g32p_familyCWMultiplicity 75 := by
  decide +kernel

theorem g32p_familyCW_certificate_076 :
    (g32p_literalCharacterValue 76 0).re = g32p_familyCWDimension 76 ∧
    (g32p_literalCharacterValue 76 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 76
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 76
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 76 j =
        g32p_familyCWDimension 76 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 76 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 76 : ℤ) -
        g32p_familyCWFixed 76 j)) = g32p_familyCWMultiplicity 76 := by
  decide +kernel

theorem g32p_familyCW_certificate_077 :
    (g32p_literalCharacterValue 77 0).re = g32p_familyCWDimension 77 ∧
    (g32p_literalCharacterValue 77 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 77
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 77
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 77 j =
        g32p_familyCWDimension 77 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 77 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 77 : ℤ) -
        g32p_familyCWFixed 77 j)) = g32p_familyCWMultiplicity 77 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_078 :
    (g32p_literalCharacterValue 78 0).re = g32p_familyCWDimension 78 ∧
    (g32p_literalCharacterValue 78 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 78
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 78
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 78 j =
        g32p_familyCWDimension 78 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 78 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 78 : ℤ) -
        g32p_familyCWFixed 78 j)) = g32p_familyCWMultiplicity 78 := by
  decide +kernel

theorem g32p_familyCW_certificate_079 :
    (g32p_literalCharacterValue 79 0).re = g32p_familyCWDimension 79 ∧
    (g32p_literalCharacterValue 79 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 79
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 79
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 79 j =
        g32p_familyCWDimension 79 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 79 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 79 : ℤ) -
        g32p_familyCWFixed 79 j)) = g32p_familyCWMultiplicity 79 := by
  decide +kernel

theorem g32p_familyCW_certificate_080 :
    (g32p_literalCharacterValue 80 0).re = g32p_familyCWDimension 80 ∧
    (g32p_literalCharacterValue 80 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 80
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 80
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 80 j =
        g32p_familyCWDimension 80 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 80 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 80 : ℤ) -
        g32p_familyCWFixed 80 j)) = g32p_familyCWMultiplicity 80 := by
  decide +kernel

theorem g32p_familyCW_certificate_081 :
    (g32p_literalCharacterValue 81 0).re = g32p_familyCWDimension 81 ∧
    (g32p_literalCharacterValue 81 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 81
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 81
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 81 j =
        g32p_familyCWDimension 81 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 81 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 81 : ℤ) -
        g32p_familyCWFixed 81 j)) = g32p_familyCWMultiplicity 81 := by
  decide +kernel

theorem g32p_familyCW_certificate_082 :
    (g32p_literalCharacterValue 82 0).re = g32p_familyCWDimension 82 ∧
    (g32p_literalCharacterValue 82 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 82
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 82
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 82 j =
        g32p_familyCWDimension 82 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 82 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 82 : ℤ) -
        g32p_familyCWFixed 82 j)) = g32p_familyCWMultiplicity 82 := by
  decide +kernel

theorem g32p_familyCW_certificate_083 :
    (g32p_literalCharacterValue 83 0).re = g32p_familyCWDimension 83 ∧
    (g32p_literalCharacterValue 83 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 83
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 83
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 83 j =
        g32p_familyCWDimension 83 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 83 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 83 : ℤ) -
        g32p_familyCWFixed 83 j)) = g32p_familyCWMultiplicity 83 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_084 :
    (g32p_literalCharacterValue 84 0).re = g32p_familyCWDimension 84 ∧
    (g32p_literalCharacterValue 84 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 84
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 84
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 84 j =
        g32p_familyCWDimension 84 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 84 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 84 : ℤ) -
        g32p_familyCWFixed 84 j)) = g32p_familyCWMultiplicity 84 := by
  decide +kernel

theorem g32p_familyCW_certificate_085 :
    (g32p_literalCharacterValue 85 0).re = g32p_familyCWDimension 85 ∧
    (g32p_literalCharacterValue 85 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 85
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 85
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 85 j =
        g32p_familyCWDimension 85 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 85 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 85 : ℤ) -
        g32p_familyCWFixed 85 j)) = g32p_familyCWMultiplicity 85 := by
  decide +kernel

theorem g32p_familyCW_certificate_086 :
    (g32p_literalCharacterValue 86 0).re = g32p_familyCWDimension 86 ∧
    (g32p_literalCharacterValue 86 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 86
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 86
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 86 j =
        g32p_familyCWDimension 86 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 86 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 86 : ℤ) -
        g32p_familyCWFixed 86 j)) = g32p_familyCWMultiplicity 86 := by
  decide +kernel

theorem g32p_familyCW_certificate_087 :
    (g32p_literalCharacterValue 87 0).re = g32p_familyCWDimension 87 ∧
    (g32p_literalCharacterValue 87 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 87
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 87
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 87 j =
        g32p_familyCWDimension 87 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 87 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 87 : ℤ) -
        g32p_familyCWFixed 87 j)) = g32p_familyCWMultiplicity 87 := by
  decide +kernel

theorem g32p_familyCW_certificate_088 :
    (g32p_literalCharacterValue 88 0).re = g32p_familyCWDimension 88 ∧
    (g32p_literalCharacterValue 88 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 88
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 88
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 88 j =
        g32p_familyCWDimension 88 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 88 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 88 : ℤ) -
        g32p_familyCWFixed 88 j)) = g32p_familyCWMultiplicity 88 := by
  decide +kernel

theorem g32p_familyCW_certificate_089 :
    (g32p_literalCharacterValue 89 0).re = g32p_familyCWDimension 89 ∧
    (g32p_literalCharacterValue 89 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 89
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 89
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 89 j =
        g32p_familyCWDimension 89 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 89 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 89 : ℤ) -
        g32p_familyCWFixed 89 j)) = g32p_familyCWMultiplicity 89 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_090 :
    (g32p_literalCharacterValue 90 0).re = g32p_familyCWDimension 90 ∧
    (g32p_literalCharacterValue 90 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 90
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 90
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 90 j =
        g32p_familyCWDimension 90 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 90 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 90 : ℤ) -
        g32p_familyCWFixed 90 j)) = g32p_familyCWMultiplicity 90 := by
  decide +kernel

theorem g32p_familyCW_certificate_091 :
    (g32p_literalCharacterValue 91 0).re = g32p_familyCWDimension 91 ∧
    (g32p_literalCharacterValue 91 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 91
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 91
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 91 j =
        g32p_familyCWDimension 91 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 91 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 91 : ℤ) -
        g32p_familyCWFixed 91 j)) = g32p_familyCWMultiplicity 91 := by
  decide +kernel

theorem g32p_familyCW_certificate_092 :
    (g32p_literalCharacterValue 92 0).re = g32p_familyCWDimension 92 ∧
    (g32p_literalCharacterValue 92 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 92
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 92
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 92 j =
        g32p_familyCWDimension 92 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 92 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 92 : ℤ) -
        g32p_familyCWFixed 92 j)) = g32p_familyCWMultiplicity 92 := by
  decide +kernel

theorem g32p_familyCW_certificate_093 :
    (g32p_literalCharacterValue 93 0).re = g32p_familyCWDimension 93 ∧
    (g32p_literalCharacterValue 93 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 93
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 93
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 93 j =
        g32p_familyCWDimension 93 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 93 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 93 : ℤ) -
        g32p_familyCWFixed 93 j)) = g32p_familyCWMultiplicity 93 := by
  decide +kernel

theorem g32p_familyCW_certificate_094 :
    (g32p_literalCharacterValue 94 0).re = g32p_familyCWDimension 94 ∧
    (g32p_literalCharacterValue 94 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 94
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 94
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 94 j =
        g32p_familyCWDimension 94 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 94 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 94 : ℤ) -
        g32p_familyCWFixed 94 j)) = g32p_familyCWMultiplicity 94 := by
  decide +kernel

theorem g32p_familyCW_certificate_095 :
    (g32p_literalCharacterValue 95 0).re = g32p_familyCWDimension 95 ∧
    (g32p_literalCharacterValue 95 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 95
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 95
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 95 j =
        g32p_familyCWDimension 95 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 95 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 95 : ℤ) -
        g32p_familyCWFixed 95 j)) = g32p_familyCWMultiplicity 95 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
