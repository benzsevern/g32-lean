# 23 tagged declarations vs the five final statement types

Legend: F = a field of the tagged structure occurs literally in the statement type; D = transitive dependency only; I = imported, not reached. A = Theorem A, B = Theorem B, C1 = Cor 8.2(i), C2 = original powers clause, S = supplied powers clause. Method: Lean.Expr.getUsedConstantsAsSet on each elaborated type. No tagged declaration is a binder of any final statement. The three F rows are fields of objects constructed on main from A (construction sites in correspondence.md).

| Tagged declaration | A | B | C1 | C2 | S |
| --- | --- | --- | --- | --- | --- |
| `AD.LefschetzOneOneFor` | D | D | D | D | D |
| `HB.AbelianVarietyCohomology` | F | D | D | F | F |
| `HB.IsCycleClassPredicate` | I | I | I | I | I |
| `HB.HodgeRingGeneratedInDegreeTwo` | I | I | I | I | I |
| `HB.LefschetzOneOne` | I | I | I | I | I |
| `HB.PolarizationTopPowerNonzero` | I | I | I | I | I |
| `HB.HardLefschetzFromDegreeTwo` | I | I | I | I | I |
| `RD.TorusCohomology` | F | D | D | F | F |
| `RD.CycleClassMultiplicative` | D | D | D | D | D |
| `RD.CupFiltered` | D | D | D | D | D |
| `RD.CycleClassIsHodge` | I | I | I | I | I |
| `RD.ComplexPointsPreconnected` | D | D | D | D | D |
| `RD.LefschetzOneOneHyp` | I | I | I | I | I |
| `RD.HardLefschetz` | I | I | I | I | I |
| `RD.AlgebraicTimesDivisor` | I | I | I | I | I |
| `RD.VanishingAboveTop` | D | D | D | D | D |
| `RD.LefschetzReflectsHodge` | I | I | I | I | I |
| `RD.SignatureDictionary` | D | D | D | D | D |
| `RD.FiniteBetti` | D | F | D | D | D |
| `RD.BettiDeRhamIso` | D | D | D | D | D |
| `RD.HodgeDecomposition` | D | D | D | D | D |
| `RD.CupProduct` | D | D | D | D | D |
| `RD.HodgeRingGeneratedByDivisorsAndWeil` | I | I | I | I | I |

