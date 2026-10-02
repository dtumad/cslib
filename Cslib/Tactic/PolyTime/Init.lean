/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Aesop

/-! # Rule sets for deterministic and probabilistic polynomial-time programs -/

public section

declare_aesop_rule_sets [PolyTime, PPT]
