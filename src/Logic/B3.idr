module Logic.B3

%default total
%access public export

||| Bochvar's internal three-valued logic */
data B3 = T | F | I

not : B3 -> B3
not T = F
not I = I
not F = T

and : B3 -> B3 -> B3
and T b = b
and I _ = I
and F I = I
and F _ = F

or : B3 -> B3 -> B3
or T I = I
or T _ = T
or I _ = I
or F b = b

impl : B3 -> B3 -> B3
impl T b = b
impl I _ = I
impl F I = I
impl F _ = T

bicond : B3 -> B3 -> B3
bicond T b = b
bicond I _ = I
bicond F T = F
bicond F I = I
bicond F F = T
