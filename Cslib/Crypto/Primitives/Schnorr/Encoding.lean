/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Oracle
public import Cslib.Computability.PolynomialTime.Encoding.Oracle

/-! # Word representations of Schnorr's hash and signing interface -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

variable {M G F : Type}

/-- Hash requests carry a message and commitment; signing requests carry a message.
The leading bit distinguishes them, leaving any ambient effects outside this interface. -/
def signatureRequestEncoding (message : Computability.Encoding M Bool)
    (element : Computability.Encoding G Bool) : Computability.Encoding ((M × G) ⊕ M) Bool :=
  (message.bitPair element).bitSum message

/-- A hash reply is a scalar; a signing reply is a commitment and response. -/
def signatureResponseEncoding (element : Computability.Encoding G Bool)
    (scalar : Computability.Encoding F Bool) : (op : (M × G) ⊕ M) →
      Computability.Encoding ((signatureEffects 0 M G F).B (.inr op)) Bool
  | .inl _ => scalar
  | .inr _ => element.bitPair scalar

end Cslib.Crypto.Schnorr
