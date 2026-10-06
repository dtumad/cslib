/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Computability.PolynomialTime.Expected

/-! Tests for probabilistic and expected polynomial time. -/

namespace CslibTests.PolynomialTime

open Turing MultiTapePTM MultiTapeTM

-- A coin flip indexed by a security parameter given in unary runs in expected polynomial time.
example : IsExpectedPolyTime (Oracle := Empty) (parameterEncoding fun _ => wordEncoding)
    (fun _ => boolEncoding)
    fun _ => (coin : (effects Empty).FreeM Bool).toResumption :=
  (isPPT_coin _).isExpectedPolyTime

end CslibTests.PolynomialTime
