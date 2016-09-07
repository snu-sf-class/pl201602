Require Import P01.

Check (test_andb31: (andb3 true true true) = true).
Check (test_andb32: (andb3 false true true) = false).
Check (test_andb33: (andb3 true false true) = false).
Check (test_andb34: (andb3 true true false) = false).
