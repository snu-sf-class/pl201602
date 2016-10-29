Require Import P03.



Check c_plus_1 : c_plus c_zero c_one = c_one.

Check c_plus_2 : c_plus c_two c_three = c_plus c_three c_two.

Check c_plus_3 :
  c_plus (c_plus c_two c_two) c_three = c_plus c_one (c_plus c_three c_three).

