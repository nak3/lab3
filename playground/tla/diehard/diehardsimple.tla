------------------------------ MODULE diehardsimple ------------------------------
\*EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC
EXTENDS Integers, TLC

Min(m,n) == IF m < n THEN m ELSE n

Max(m,n) == IF m > n THEN m ELSE n

(***************************************************************************

--algorithm diehardsimple {
    variables big = 0, small = 0;
    process (Proc = 1)

  {a: while(TRUE) {
\* full
       either {
        big := 5
       } or {
        small := 3
       } or {
\* flush
        big := 0
       } or {
        small := 0
\* small to big
       } or if ((big + small) > 5) {
        small := small - (5 - big);
        big := 5;
       } or if ((big + small) =< 5) {
        big := big + small;
        small := 0;
\* big to small
       } or if ((big + small) > 3) {
        big := big - (3-small);
        small := 3;
       } or if ((big + small) =< 3) {
        small := small + big;
        big := 0;
       };
       print <<"big bucket-> ", big>>;
    };
  }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES big, small

vars == << big, small >>

ProcSet == {1}

Init == (* Global variables *)
        /\ big = 0
        /\ small = 0

Proc == /\ \/ /\ big' = 5
              /\ small' = small
           \/ /\ small' = 3
              /\ big' = big
           \/ /\ big' = 0
              /\ small' = small
           \/ /\ small' = 0
              /\ big' = big
           \/ /\ IF (big + small) > 5
                    THEN /\ small' = small - (5 - big)
                         /\ big' = 5
                    ELSE /\ TRUE
                         /\ UNCHANGED << big, small >>
           \/ /\ IF (big + small) =< 5
                    THEN /\ big' = big + small
                         /\ small' = 0
                    ELSE /\ TRUE
                         /\ UNCHANGED << big, small >>
           \/ /\ IF (big + small) > 3
                    THEN /\ big' = big - (3-small)
                         /\ small' = 3
                    ELSE /\ TRUE
                         /\ UNCHANGED << big, small >>
           \/ /\ IF (big + small) =< 3
                    THEN /\ small' = small + big
                         /\ big' = 0
                    ELSE /\ TRUE
                         /\ UNCHANGED << big, small >>
        /\ PrintT(<<"big bucket-> ", big'>>)

Next == Proc

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Dec 21 23:03:58 JST 2016 by knakayam
\* Created Wed Dec 21 16:31:08 JST 2016 by knakayam
