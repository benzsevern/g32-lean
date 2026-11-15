import HodgeLean.Foundations.Program.PrymVariationLatticeArithmetic

set_option maxHeartbeats 400000

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers

def b63l_zwZero : HurwitzPrymRex_Zw := ⟨0, 0⟩

def b63l_zwNsmul (n : ℤ) (x : HurwitzPrymRex_Zw) : HurwitzPrymRex_Zw :=
  ⟨n * x.re, n * x.om⟩

def b63l_matZero : HurwitzPrymRex_Mat := fun _ _ ↦ b63l_zwZero

def b63l_matAdd (A B : HurwitzPrymRex_Mat) : HurwitzPrymRex_Mat := fun i j ↦
  HurwitzPrymRex_Zw.add (A i j) (B i j)

def b63l_matNsmul (n : ℤ) (A : HurwitzPrymRex_Mat) : HurwitzPrymRex_Mat := fun i j ↦
  b63l_zwNsmul n (A i j)

def b63l_projectorWeight (A : HurwitzPrymRex_Mat) : ℤ :=
  6 * (A 0 0).re - 3 * (A 0 0).om - 6 * (A 0 1).re + 3 * (A 0 1).om -
    3 * (A 0 2).om + 3 * (A 0 3).re

def b63l_projectorTerm (A : HurwitzPrymRex_Mat) : HurwitzPrymRex_Mat :=
  b63l_matNsmul (b63l_projectorWeight A) A

def b63l_projectorRawEnumeration : List HurwitzPrymRex_Mat :=
  HurwitzPrymRex_g32TOne.flatMap fun A ↦
    HurwitzPrymRex_g32TTwo.flatMap fun B ↦
      HurwitzPrymRex_g32TThree.map fun C ↦
        HurwitzPrymRex_mmul A (HurwitzPrymRex_mmul B C)

def b63l_projectorAggregate : HurwitzPrymRex_Mat :=
  b63l_projectorRawEnumeration.foldl
    (fun S A ↦ b63l_matAdd S (b63l_projectorTerm A)) b63l_matZero

def b63l_projectorEntry (i j : Fin 4) : HurwitzPrymRex_Zw :=
  b63l_projectorRawEnumeration.foldl
    (fun S A ↦ HurwitzPrymRex_Zw.add S (b63l_projectorTerm A i j)) b63l_zwZero

noncomputable def b63l_projectorEnumeration : List (Matrix (Fin 4) (Fin 4) ℂ) :=
  b63l_projectorRawEnumeration.map fun A ↦
        HurwitzPrymRex_g32conj
          (HurwitzPrymRex_evM g32h_omega A)

def b63l_projectorTarget : HurwitzPrymRex_Mat := fun i j ↦
  if j = 0 then
    if i = 0 then ⟨116640, 0⟩
    else if i = 1 then ⟨-116640, 0⟩
    else if i = 2 then ⟨38880, 77760⟩
    else ⟨38880, -38880⟩
  else ⟨0, 0⟩

end HodgeLean.Foundations.Program
