------------------------------- MODULE euclidsimple -------------------------------

EXTENDS Integers, TLC

(***************************************************************************
--algorithm euclidsimple {
  process (Proc = 1)
  variables m=30, n=18, u=m, v=n;
  { 
    a: while (u # 0) {
      if (u < v) {
        u := v || v := u;
      };
      b: u := u - v;
    };
    print <<m, n, "have gdc",v>>;
  }
}

***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES pc, m, n, u, v

vars == << pc, m, n, u, v >>

ProcSet == {1}

Init == (* Process Proc *)
        /\ m = 30
        /\ n = 18
        /\ u = m
        /\ v = n
        /\ pc = [self \in ProcSet |-> "a"]

a == /\ pc[1] = "a"
     /\ IF u # 0
           THEN /\ IF u < v
                      THEN /\ /\ u' = v
                              /\ v' = u
                      ELSE /\ TRUE
                           /\ UNCHANGED << u, v >>
                /\ pc' = [pc EXCEPT ![1] = "b"]
           ELSE /\ PrintT(<<m, n, "have gdc",v>>)
                /\ pc' = [pc EXCEPT ![1] = "Done"]
                /\ UNCHANGED << u, v >>
     /\ UNCHANGED << m, n >>

b == /\ pc[1] = "b"
     /\ u' = u - v
     /\ pc' = [pc EXCEPT ![1] = "a"]
     /\ UNCHANGED << m, n, v >>

Proc == a \/ b

Next == Proc
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Dec 22 15:26:06 JST 2016 by knakayam
\* Created Thu Dec 22 15:18:01 JST 2016 by knakayam
