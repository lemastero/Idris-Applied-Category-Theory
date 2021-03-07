module Logic.ActBool

%default total
%access public export

||| Bool binary ops
||| | A | B | AND | OR | XOR | IMPLY | NAND | NOR | XNOR | NIMPLY | converse | nconverse | fst | snd | false | true | nsnd | nfst |
||| |---|---|-----|----|-----|-------|------|-----|------|--------|----------|-----------|-----|-----|-------|------|------|------|
||| | 0 | 0 | 0   | 0  |  0  | 1     | 1    | 1   | 1    | 0      | 1        | 0         | 0   | 0   | 0     | 1    | 1    | 1    |
||| | 0 | 1 | 0   | 1  |  1  | 1     | 1    | 0   | 0    | 0      | 0        | 1         | 0   | 1   | 0     | 1    | 0    | 1    |
||| | 1 | 0 | 0   | 1  |  1  | 0     | 1    | 0   | 0    | 1      | 1        | 0         | 1   | 0   | 0     | 1    | 1    | 0    |
||| | 1 | 1 | 1   | 1  |  0  | 1     | 0    | 0   | 1    | 0      | 1        | 0         | 1   | 1   | 0     | 1    | 0    | 0    |

xor : Bool -> Bool -> Bool
xor True True = False
xor False False = False
xor _ _ = True

impl : Bool -> Bool -> Bool
impl True False = False
impl _ _ = True

nand : Bool -> Bool -> Bool
nand a b = not (a && b)

nor : Bool -> Bool -> Bool
nor a b = not (a || b)

xnor : Bool -> Bool -> Bool
xnor a b = not (xor a b)

converse : Bool -> Bool -> Bool
converse False True = False
converse _ _ = True
