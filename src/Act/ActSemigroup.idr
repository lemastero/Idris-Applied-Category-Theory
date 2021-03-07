module Act.ActSemigroup

import Act.Magma

%default total
%access public export

interface Magma t => ActSemigroup t where
  combine : t -> t -> t
  associativity : {a : t} -> {b : t} -> {c : t} ->
    combine (combine a b) c = combine a (combine b c)
