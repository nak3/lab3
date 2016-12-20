------------------------------ MODULE fizzbuzz ------------------------------

EXTENDS Integers, TLC
(***************************************************************************

--algorithm fizzbuzz {
    variables x = 1;
\*    process (Proc \in 1..2)
    process (Proc = 1)
    variables y = 0;
    {a: while(x <= 30) {
\*        print <<"value is ", x>>;
    
        if (x % 15 = 0) {
            print <<"FizzBuzz", x>>;
        } else if (x % 3 = 0) {
            print <<"Fizz", x>>;
        } else if (x % 5 = 0) {
            print <<"Buzz", x>>;
        };
        y := x;
        x := y + 1;                
        };
    };
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, pc, y

vars == << x, pc, y >>

ProcSet == {1}

Init == (* Global variables *)
        /\ x = 1
        (* Process Proc *)
        /\ y = 0
        /\ pc = [self \in ProcSet |-> "a"]

a == /\ pc[1] = "a"
     /\ IF x <= 30
           THEN /\ IF x % 15 = 0
                      THEN /\ PrintT(<<"FizzBuzz", x>>)
                      ELSE /\ IF x % 3 = 0
                                 THEN /\ PrintT(<<"Fizz", x>>)
                                 ELSE /\ IF x % 5 = 0
                                            THEN /\ PrintT(<<"Buzz", x>>)
                                            ELSE /\ TRUE
                /\ y' = x
                /\ x' = y' + 1
                /\ pc' = [pc EXCEPT ![1] = "a"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                /\ UNCHANGED << x, y >>

Proc == a

Next == Proc
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Dec 20 23:04:15 JST 2016 by knakayam
\* Created Tue Dec 20 22:01:29 JST 2016 by knakayam
