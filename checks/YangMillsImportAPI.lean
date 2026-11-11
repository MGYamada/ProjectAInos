/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos

/-! A public API smoke test for the independently ported Yang--Mills modules.
    This file checks the names and types, not the physical validity of any
    specified construction or positive-mass-gap claim. -/

#check YM.Analytic.param
#check YM.Analysis.sym_Jet
#check YM.Tensor.Euler
#check YM.Kernel.host
#check YM.Wilson.law
#check YM.Wilson.law_gauge
#check YangMills.WilsonFamily.Converges
#check YangMills.JointExistence
#check ProjectAInos.Variational.jet_derivative_eq_ym_directional

example : YangMills.JointExistence → YangMills.JointExistence := id
