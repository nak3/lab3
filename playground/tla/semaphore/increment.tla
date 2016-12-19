----------------------------- MODULE increment -----------------------------

EXTENDS Integers, TLC

(* PlusCal options (sf) *)
(***************************************************************************

--algorithm Increment {

variables x = 0;
          s = 0;      (* Shared semaphore *)

macro P(sem) { await sem >= 0; sem := sem - 1;}
macro V(sem) { sem := sem + 1 }

process (Proc \in 1..2)
variables y = 0;

    {
        lock: P(s);
        l0:   y := x + 1;
        l1:   x := y;
        unlock: V(s);
    };
    
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, s, pc, y

vars == << x, s, pc, y >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ x = 0
        /\ s = 0
        (* Process Proc *)
        /\ y = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> "lock"]

lock(self) == /\ pc[self] = "lock"
              /\ s >= 0
              /\ s' = s - 1
              /\ pc' = [pc EXCEPT ![self] = "l0"]
              /\ UNCHANGED << x, y >>

l0(self) == /\ pc[self] = "l0"
            /\ y' = [y EXCEPT ![self] = x + 1]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << x, s >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = y[self]
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ UNCHANGED << s, y >>

unlock(self) == /\ pc[self] = "unlock"
                /\ s' = s + 1
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << x, y >>

Proc(self) == lock(self) \/ l0(self) \/ l1(self) \/ unlock(self)

Next == (\E self \in 1..2: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : SF_vars(Proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Mon Dec 19 21:19:26 JST 2016 by knakayam
\* Created Sun Dec 18 23:20:21 JST 2016 by knakayam
