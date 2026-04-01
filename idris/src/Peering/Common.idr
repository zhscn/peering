||| Shared primitive aliases used across the image-native peering model.
module Peering.Common

import Data.Nat

%default total

public export
Epoch : Type
Epoch = Nat

public export
OsdId : Type
OsdId = Nat

public export
PgId : Type
PgId = Nat

public export
Length : Type
Length = Nat

public export
ObjectId : Type
ObjectId = Nat
