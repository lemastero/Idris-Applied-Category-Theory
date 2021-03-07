module Act.Magma

%default total
%access public export

interface Magma ty where
  combine : ty -> ty -> ty
