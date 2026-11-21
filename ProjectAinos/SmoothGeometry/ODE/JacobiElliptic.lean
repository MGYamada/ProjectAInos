/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.JacobiElliptic

/-! Compatibility names for the original Jacobi elliptic function module. -/

@[expose] public section

namespace ProjectAinos.SmoothGeometry.JacobiElliptic

export ProjectAinos.SpecialFunctions.JacobiElliptic
  (amplitudeField one_sub_pos amplitudeField_pos amplitudeField_sq abs_amplitudeField_le
   amplitudeField_add_pi contDiff_amplitudeField hasDerivAt_amplitudeField am sn cn dn
   halfPeriod am_zero sn_zero cn_zero dn_zero sn_sq_add_cn_sq dn_sq dn_pos hasDerivAt_am
   hasDerivAt_sn hasDerivAt_cn hasDerivAt_dn contDiff_am contDiff_sn contDiff_cn contDiff_dn
   am_surjective strictMono_am halfPeriod_pos am_add_halfPeriod sn_add_halfPeriod
   cn_add_halfPeriod dn_add_halfPeriod)

end ProjectAinos.SmoothGeometry.JacobiElliptic
