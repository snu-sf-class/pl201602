Require Import P04.



Check c_mult_1 : c_mult c_one c_one = c_one.

Check c_mult_2 : c_mult c_zero (c_plus c_three c_three) = c_zero.

Check c_mult_3 : c_mult c_two c_three = c_plus c_three c_three.


