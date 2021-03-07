module Act.SymmetricMonoid

import Act.ActMonoid

%default total
%access public export

interface ActMonoid ty => SymmetricMonoid ty where
  combine : ty -> ty -> ty
  I : ty
  leftUnitality : {a : ty} ->
    combine I a = a
  rightUnitality : {a : ty} ->
    a = combine a I
  associativity : {a : ty} -> {b : ty} -> {c : ty} ->
    combine (combine a b) c = combine a (combine b c)
  symmetry : {a : ty} -> {b : ty} ->
    (combine a b) = (combine b a)
