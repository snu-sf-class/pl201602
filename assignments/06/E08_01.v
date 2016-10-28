Require Import P08.



Check subseq_ex1: subseq [1;2;3] [1;2;3].

Check subseq_ex2: subseq [1;2;3] [1;1;1;2;2;3].

Check subseq_ex3: subseq [1;2;3] [1;2;7;3].

Check subseq_ex4: subseq [1;2;3] [5;6;1;9;9;2;7;3;8].

Check subseq_ex5: ~ subseq [1;2;3] [1;2].

Check subseq_ex6: ~ subseq [1;2;3] [1;3].

Check subseq_ex7: ~ subseq [1;2;3] [5;6;2;1;7;3;8].

