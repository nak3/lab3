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
