module Act.ActMonoid

import Act.ActSemigroup

%default total
%access public export

interface ActSemigroup ty => ActMonoid ty where
  combine : ty -> ty -> ty
  I : ty
  leftUnitality : {a : ty} ->
    combine I a = a
  rightUnitality : {a : ty} ->
    a = combine a I
  associativity : {a : ty} -> {b : ty} -> {c : ty} ->
    combine (combine a b) c = combine a (combine b c)
