import HodgeLean.Foundations.Program.RigidStartingSystemDefs

noncomputable section
open Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

def b65r_leftWords (w : ℂ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![1, g32R2 w, g32X w, g32X w * g32R2 w]

def b65r_rightWords (w : ℂ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![1, g32R2 w, g32X w, g32R2 w * g32X w]

def b65r_reflectionVector (w : ℂ) : Fin 4 → ℂ := ![w, -1, 0, 1]

def b65r_reflectionRow (w : ℂ) : Fin 4 → ℂ := ![(w+2)/3, (1-w)/3, 0, (w-1)/3]

def b65r_cyclicColumns (w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![w, 0, -w, 0;
     -1, w, 1, 1-w;
     0, w+1, 0, 0;
     1, 1, w+1, 0]

def b65r_cyclicColumnsInverse (w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-2*w/3-1/3, 0, 2*w/3+1/3, 1/3-w/3;
     0, 0, -w, 0;
     w/3+2/3, 0, 2*w/3+1/3, 1/3-w/3;
     -2*w/3-1/3, w/3+2/3, -2*w/3-1/3, 0]

def b65r_cyclicRows (w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![w/3+2/3, 1/3-w/3, 0, w/3-1/3;
     1/3-w/3, 0, w/3-1/3, w/3-1/3;
     -w/3-2/3, 0, -2*w/3-1/3, -2*w/3-1/3;
     w/3-1/3, 0, 1/3-w/3, -w/3-2/3]

def b65r_cyclicRowsInverse (w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, w+1, w, 0;
     w+2, -w-1, 1, -1;
     0, 0, w, 1;
     0, -1, 0, -1]

end HodgeLean.Foundations.Program
