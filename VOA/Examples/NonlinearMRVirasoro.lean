/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.NonlinearMR
import VOA.Examples.NonlinearVirasoroGenuine

/-!
# The full De Sole–Kac relation space for Virasoro is the kernel of `Φ`

For the Virasoro OPE, the full relation space of any non-linear extension `NP` coincides with the
two-generator relation space (`MRfull_virasoro`), and the latter is the kernel of the explicit map
`Φ_Vir` (`MRtwoCar_eq_ker_PhiVir`).  Composing the two gives `M_full = ker Φ_Vir`.

The statement is parametric in `NP : NPExtension (virasoroOPE c)`; no instance of `NPExtension` is
constructed in the library.
-/

namespace VOA.NonlinearConformal

open VOA.VirModule

/-- **`M_full = ker Φ` for the Virasoro OPE.** -/
theorem MRfullCar_virasoro_eq_ker_PhiVir (c : ℂ) (NP : NPExtension (virasoroOPE c)) :
    MRfullCar NP = LinearMap.ker (PhiVir c) :=
  (MRfull_virasoro c NP).trans (MRtwoCar_eq_ker_PhiVir c)

end VOA.NonlinearConformal
