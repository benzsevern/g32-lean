import HodgeLean.Foundations.AnalyticSubset

/-! Coordinate derivatives used for countable hypersurface covers. -/

noncomputable section
namespace HodgeLean.Foundations

/-- Successive coordinate derivatives, with the empty word acting as the identity.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Chapter I,
§A (partial derivatives of holomorphic functions). -/
def astrat_partial (n : ℕ) (f : (Fin n → ℂ) → ℂ) :
    List (Fin n) → (Fin n → ℂ) → ℂ
  | [] => f
  | i :: s => fun z => fderiv ℂ (astrat_partial n f s) z (Pi.single i 1)

example : astrat_partial 1 (fun z => z 0) [] 0 = 0 := rfl

end HodgeLean.Foundations
