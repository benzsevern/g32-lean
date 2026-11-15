import HodgeLean.Foundations.Program.MilneTensorPairedLocal
import HodgeLean.Foundations.Program.MilneTensorSchurPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_pairBasisVector (d : ℕ) : (Fin 2 ⊕ Fin d) → (Fin 2 → ℂ) × (Fin d → ℂ) :=
  Sum.elim (fun i => (Pi.single i 1, 0)) (fun i => (0, Pi.single i 1))

def m1b_pairFormPoint {d r n : ℕ}
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × (Fin d → ℂ)))
    (v : Fin n → Fin r → (Fin 2 → ℂ) × (Fin d → ℂ)) :
    (((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕ (Fin n × (Fin r × (Fin 2 ⊕ Fin d)))) → ℂ :=
  Sum.elim (fun ij => Q (m1b_pairBasisVector d ij.1) (m1b_pairBasisVector d ij.2))
    (fun jc => Sum.elim (v jc.1 jc.2.1).1 (v jc.1 jc.2.1).2 jc.2.2)

end HodgeLean.Foundations.Program
