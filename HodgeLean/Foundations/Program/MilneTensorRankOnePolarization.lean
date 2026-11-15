import HodgeLean.Foundations.Program.MilneTensorRankOneForm
import HodgeLean.Foundations.Program.MilneTensorMultilinearFlip
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def m1b_rankOnePolarization (k : ℕ)
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ)) :
    MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ) ℂ) :=
  ((m1b_multilinearFlip J).compMultilinearMap (fun _ => m1b_rankOneForm)).domDomCongr
    ((Equiv.sigmaEquivProd (Fin k) (Fin 2)).trans finProdFinEquiv)

theorem m1b_rankOnePolarization_apply (k : ℕ)
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ))
    (x v : Fin (k * 2) → ι → ℂ) :
    m1b_rankOnePolarization k J x v =
      J v (fun a => m1b_rankOneForm (fun s => x (finProdFinEquiv (a, s)))) := rfl

end HodgeLean.Foundations.Program
