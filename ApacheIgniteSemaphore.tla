----------------------- MODULE ApacheIgniteSemaphore -----------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

(***************************************************************************
--algorithm GridCacheSemaphoreImpl {

variables
    procs =  1..5;
    count = 3;
    k = count;
    waiters = [p \in procs  |-> 0];
    
define {
    ExcInv == \E prcs \in SUBSET procs: 
            (\A p \in prcs : pc[p] = "u2") 
            /\ (\A q \in (procs \ prcs): pc[q] # "u2")
            /\ Cardinality(prcs) <= k                    
}

procedure acquire(acquires)

variables 
    available;
    waitingCnt;
    remaining; 
    retVal;
    
{    
a1:    while (TRUE) {

           available := count;
           remaining := available - acquires;
           
           await remaining >= 0;
                
           retVal := FALSE;
a2:        if (count = available) {
               retVal := TRUE
           };
        
           if (retVal) {
            
               waitingCnt := available - remaining + waiters[self];

               waiters[self] := waitingCnt;
            
               count := remaining;
               
a3:            return
               
           };
                
       } 
}

procedure release(releases)

variables 
    available;
    waitingCnt;
    remaining;
    retVal;
    
{     
r1:    while (TRUE) {

           available := count;
           remaining := available + releases;
                
           retVal := FALSE;
r2:        if (count = available) {
               retVal := TRUE
           };
        
           if (retVal) {

               waitingCnt := available - remaining + waiters[self];

               waiters[self] := waitingCnt;
            
               count := remaining;
               
r3:            return

           };
                
       } 
}

process (proc \in procs)
    {
u1:   while (TRUE) {
            call acquire(1);
u2:         skip;
u3:         call release(1);
      }
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
\* Procedure variable available of procedure acquire at line 23 col 5 changed to available_
\* Procedure variable waitingCnt of procedure acquire at line 24 col 5 changed to waitingCnt_
\* Procedure variable remaining of procedure acquire at line 25 col 5 changed to remaining_
\* Procedure variable retVal of procedure acquire at line 26 col 5 changed to retVal_
CONSTANT defaultInitValue
VARIABLES procs, count, k, waiters, pc, stack

(* define statement *)
ExcInv == \E prcs \in SUBSET procs:
        (\A p \in prcs : pc[p] = "u2")
        /\ (\A q \in (procs \ prcs): pc[q] # "u2")
        /\ Cardinality(prcs) <= k

VARIABLES acquires, available_, waitingCnt_, remaining_, retVal_, releases, 
          available, waitingCnt, remaining, retVal

vars == << procs, count, k, waiters, pc, stack, acquires, available_, 
           waitingCnt_, remaining_, retVal_, releases, available, waitingCnt, 
           remaining, retVal >>

ProcSet == (procs)

Init == (* Global variables *)
        /\ procs = 1..5
        /\ count = 3
        /\ k = count
        /\ waiters = [p \in procs  |-> 0]
        (* Procedure acquire *)
        /\ acquires = [ self \in ProcSet |-> defaultInitValue]
        /\ available_ = [ self \in ProcSet |-> defaultInitValue]
        /\ waitingCnt_ = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining_ = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure release *)
        /\ releases = [ self \in ProcSet |-> defaultInitValue]
        /\ available = [ self \in ProcSet |-> defaultInitValue]
        /\ waitingCnt = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "u1"]

a1(self) == /\ pc[self] = "a1"
            /\ available_' = [available_ EXCEPT ![self] = count]
            /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
            /\ remaining_'[self] >= 0
            /\ retVal_' = [retVal_ EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << procs, count, k, waiters, stack, acquires, 
                            waitingCnt_, releases, available, waitingCnt, 
                            remaining, retVal >>

a2(self) == /\ pc[self] = "a2"
            /\ IF count = available_[self]
                  THEN /\ retVal_' = [retVal_ EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal_
            /\ IF retVal_'[self]
                  THEN /\ waitingCnt_' = [waitingCnt_ EXCEPT ![self] = available_[self] - remaining_[self] + waiters[self]]
                       /\ waiters' = [waiters EXCEPT ![self] = waitingCnt_'[self]]
                       /\ count' = remaining_[self]
                       /\ pc' = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a1"]
                       /\ UNCHANGED << count, waiters, waitingCnt_ >>
            /\ UNCHANGED << procs, k, stack, acquires, available_, remaining_, 
                            releases, available, waitingCnt, remaining, retVal >>

a3(self) == /\ pc[self] = "a3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ waitingCnt_' = [waitingCnt_ EXCEPT ![self] = Head(stack[self]).waitingCnt_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ retVal_' = [retVal_ EXCEPT ![self] = Head(stack[self]).retVal_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << procs, count, k, waiters, releases, available, 
                            waitingCnt, remaining, retVal >>

acquire(self) == a1(self) \/ a2(self) \/ a3(self)

r1(self) == /\ pc[self] = "r1"
            /\ available' = [available EXCEPT ![self] = count]
            /\ remaining' = [remaining EXCEPT ![self] = available'[self] + releases[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << procs, count, k, waiters, stack, acquires, 
                            available_, waitingCnt_, remaining_, retVal_, 
                            releases, waitingCnt >>

r2(self) == /\ pc[self] = "r2"
            /\ IF count = available[self]
                  THEN /\ retVal' = [retVal EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal
            /\ IF retVal'[self]
                  THEN /\ waitingCnt' = [waitingCnt EXCEPT ![self] = available[self] - remaining[self] + waiters[self]]
                       /\ waiters' = [waiters EXCEPT ![self] = waitingCnt'[self]]
                       /\ count' = remaining[self]
                       /\ pc' = [pc EXCEPT ![self] = "r3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r1"]
                       /\ UNCHANGED << count, waiters, waitingCnt >>
            /\ UNCHANGED << procs, k, stack, acquires, available_, waitingCnt_, 
                            remaining_, retVal_, releases, available, 
                            remaining >>

r3(self) == /\ pc[self] = "r3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ waitingCnt' = [waitingCnt EXCEPT ![self] = Head(stack[self]).waitingCnt]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << procs, count, k, waiters, acquires, available_, 
                            waitingCnt_, remaining_, retVal_ >>

release(self) == r1(self) \/ r2(self) \/ r3(self)

u1(self) == /\ pc[self] = "u1"
            /\ /\ acquires' = [acquires EXCEPT ![self] = 1]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire",
                                                        pc        |->  "u2",
                                                        available_ |->  available_[self],
                                                        waitingCnt_ |->  waitingCnt_[self],
                                                        remaining_ |->  remaining_[self],
                                                        retVal_   |->  retVal_[self],
                                                        acquires  |->  acquires[self] ] >>
                                                    \o stack[self]]
            /\ available_' = [available_ EXCEPT ![self] = defaultInitValue]
            /\ waitingCnt_' = [waitingCnt_ EXCEPT ![self] = defaultInitValue]
            /\ remaining_' = [remaining_ EXCEPT ![self] = defaultInitValue]
            /\ retVal_' = [retVal_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << procs, count, k, waiters, releases, available, 
                            waitingCnt, remaining, retVal >>

u2(self) == /\ pc[self] = "u2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << procs, count, k, waiters, stack, acquires, 
                            available_, waitingCnt_, remaining_, retVal_, 
                            releases, available, waitingCnt, remaining, retVal >>

u3(self) == /\ pc[self] = "u3"
            /\ /\ releases' = [releases EXCEPT ![self] = 1]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release",
                                                        pc        |->  "u1",
                                                        available |->  available[self],
                                                        waitingCnt |->  waitingCnt[self],
                                                        remaining |->  remaining[self],
                                                        retVal    |->  retVal[self],
                                                        releases  |->  releases[self] ] >>
                                                    \o stack[self]]
            /\ available' = [available EXCEPT ![self] = defaultInitValue]
            /\ waitingCnt' = [waitingCnt EXCEPT ![self] = defaultInitValue]
            /\ remaining' = [remaining EXCEPT ![self] = defaultInitValue]
            /\ retVal' = [retVal EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "r1"]
            /\ UNCHANGED << procs, count, k, waiters, acquires, available_, 
                            waitingCnt_, remaining_, retVal_ >>

proc(self) == u1(self) \/ u2(self) \/ u3(self)

Next == (\E self \in ProcSet: acquire(self) \/ release(self))
           \/ (\E self \in procs: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Wed May 06 04:57:33 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
