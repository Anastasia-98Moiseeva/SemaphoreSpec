----------------------- MODULE ApacheIgniteSemaphore -----------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS PROCS,
          SEMAFORE_CAPACITY,     
          NUM_OF_PERMITS
          
ASSUME /\ SEMAFORE_CAPACITY \in Nat\{0}
       /\ NUM_OF_PERMITS \in Nat\{0}
       /\ SEMAFORE_CAPACITY >= NUM_OF_PERMITS

(***************************************************************************
--algorithm GridCacheSemaphoreImpl {

variables
    count = SEMAFORE_CAPACITY;
    acqRMState = [rm \in PROCS |-> "not init"];
    relRMState = [rm \in PROCS |-> "not init"];  
    
define {
    TypeInv == count \in 0..SEMAFORE_CAPACITY
    ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) <= SEMAFORE_CAPACITY   
     
    TCTypeInv == \A rm \in PROCS : /\ acqRMState[rm] \in {"not init", "working", "prepared", "commited", "aborted"}
                                   /\ relRMState[rm] \in {"not init", "working", "prepared", "commited", "aborted"}
                                                       
    TCConsistentInv == \A rm1, rm2 \in PROCS : /\ ~ /\ acqRMState[rm1] = "aborted"
                                                    /\ acqRMState[rm2] = "committed"                      
                                               /\ ~ /\ relRMState[rm1] = "aborted"
                                                    /\ relRMState[rm2] = "committed"
    
    CanCommit(rmState) == \A rm \in PROCS : rmState[rm] \in {"prepared", "committed"}
    NotCommitted(rmState) == \A rm \in PROCS : rmState[rm] # "committed" 
}

macro start_transaction(rmState)
{
       rmState := [rm \in PROCS |-> "working"];
}

macro prepare(p, rmState)
{
       await rmState[p] =  "working";
       rmState[p] := "prepared";  
}

macro decide(p, rmState)
{
       either { 
           await /\ rmState[p] = "prepared"
                 /\ CanCommit(rmState);
           rmState[p] := "commited";
       }
       or {
           await \/ rmState[p] = "working"
                 \/ /\ rmState[p] = "prepared"
                    /\ NotCommitted(rmState);
           rmState[p] := "aborted";
       }    
}

procedure commit_acquire_transaction()
{
tca:   while (acqRMState[self] \in {"working", "prepared"}){
            either prepare(self, acqRMState) or decide(self, acqRMState)
       };
       return
}

procedure commit_release_transaction()
{
tcr:   while (relRMState[self] \in {"working", "prepared"}){
            either prepare(self, relRMState) or decide(self, relRMState)
       };
       return
}

procedure acquire(acquires)

variables 
    available;
    remaining; 
    retVal;
    
{    
a1:    while (TRUE) {

           available := count;
           remaining := available - acquires;  
                    
           await remaining >= 0;  
                     
as:        start_transaction(acqRMState);  
           
a2:        retVal := FALSE;
a3:        if (count = available) {
a4:            retVal := TRUE
           };
                  
a5:        if (retVal) {  
                   
ac:            call commit_acquire_transaction();

a6:            if (acqRMState[self] = "commited"){

                    count := remaining;
                    
a7:                 return
               };             
           }  
       } 
}

procedure release(releases)

variables 
    available;
    remaining;
    retVal;
    
{     
r1:    while (TRUE) {

           available := count;
           remaining := available + releases;
           
rs:        start_transaction(relRMState); 
                                  
r2:        retVal := FALSE;
r3:        if (count = available) {
r4:            retVal := TRUE
           };      
           
r5:        if (retVal) {
                     
rc:            call commit_release_transaction();

r6:            if (relRMState[self] = "commited"){

                    count := remaining;
                    
r7:                 return
               };
           }           
       } 
}

process (proc \in PROCS)
    {
u1:   while (TRUE) {
            call acquire(NUM_OF_PERMITS);
u2:         skip;
u3:         call release(NUM_OF_PERMITS);
      }
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATIONNUMberNUMberNUMber
\* Procedure variable available of procedure acquire at line 81 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 82 col 5 changed to remaining_
\* Procedure variable retVal of procedure acquire at line 83 col 5 changed to retVal_
CONSTANT defaultInitValue
VARIABLES count, acqRMState, relRMState, pc, stack

(* define statement *)
TypeInv == count \in 0..SEMAFORE_CAPACITY
ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) <= SEMAFORE_CAPACITY

TCTypeInv == \A rm \in PROCS : /\ acqRMState[rm] \in {"not init", "working", "prepared", "commited", "aborted"}
                               /\ relRMState[rm] \in {"not init", "working", "prepared", "commited", "aborted"}

TCConsistentInv == \A rm1, rm2 \in PROCS : /\ ~ /\ acqRMState[rm1] = "aborted"
                                                /\ acqRMState[rm2] = "committed"
                                           /\ ~ /\ relRMState[rm1] = "aborted"
                                                /\ relRMState[rm2] = "committed"

CanCommit(rmState) == \A rm \in PROCS : rmState[rm] \in {"prepared", "committed"}
NotCommitted(rmState) == \A rm \in PROCS : rmState[rm] # "committed"

VARIABLES acquires, available_, remaining_, retVal_, releases, available, 
          remaining, retVal

vars == << count, acqRMState, relRMState, pc, stack, acquires, available_, 
           remaining_, retVal_, releases, available, remaining, retVal >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = SEMAFORE_CAPACITY
        /\ acqRMState = [rm \in PROCS |-> "not init"]
        /\ relRMState = [rm \in PROCS |-> "not init"]
        (* Procedure acquire *)
        /\ acquires = [ self \in ProcSet |-> defaultInitValue]
        /\ available_ = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining_ = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure release *)
        /\ releases = [ self \in ProcSet |-> defaultInitValue]
        /\ available = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "u1"]

tca(self) == /\ pc[self] = "tca"
             /\ IF acqRMState[self] \in {"working", "prepared"}
                   THEN /\ \/ /\ acqRMState[self] =  "working"
                              /\ acqRMState' = [acqRMState EXCEPT ![self] = "prepared"]
                           \/ /\ \/ /\ /\ acqRMState[self] = "prepared"
                                       /\ CanCommit(acqRMState)
                                    /\ acqRMState' = [acqRMState EXCEPT ![self] = "commited"]
                                 \/ /\ \/ acqRMState[self] = "working"
                                       \/ /\ acqRMState[self] = "prepared"
                                          /\ NotCommitted(acqRMState)
                                    /\ acqRMState' = [acqRMState EXCEPT ![self] = "aborted"]
                        /\ pc' = [pc EXCEPT ![self] = "tca"]
                        /\ stack' = stack
                   ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED acqRMState
             /\ UNCHANGED << count, relRMState, acquires, available_, 
                             remaining_, retVal_, releases, available, 
                             remaining, retVal >>

commit_acquire_transaction(self) == tca(self)

tcr(self) == /\ pc[self] = "tcr"
             /\ IF relRMState[self] \in {"working", "prepared"}
                   THEN /\ \/ /\ relRMState[self] =  "working"
                              /\ relRMState' = [relRMState EXCEPT ![self] = "prepared"]
                           \/ /\ \/ /\ /\ relRMState[self] = "prepared"
                                       /\ CanCommit(relRMState)
                                    /\ relRMState' = [relRMState EXCEPT ![self] = "commited"]
                                 \/ /\ \/ relRMState[self] = "working"
                                       \/ /\ relRMState[self] = "prepared"
                                          /\ NotCommitted(relRMState)
                                    /\ relRMState' = [relRMState EXCEPT ![self] = "aborted"]
                        /\ pc' = [pc EXCEPT ![self] = "tcr"]
                        /\ stack' = stack
                   ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED relRMState
             /\ UNCHANGED << count, acqRMState, acquires, available_, 
                             remaining_, retVal_, releases, available, 
                             remaining, retVal >>

commit_release_transaction(self) == tcr(self)

a1(self) == /\ pc[self] = "a1"
            /\ available_' = [available_ EXCEPT ![self] = count]
            /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
            /\ remaining_'[self] >= 0
            /\ pc' = [pc EXCEPT ![self] = "as"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            retVal_, releases, available, remaining, retVal >>

as(self) == /\ pc[self] = "as"
            /\ acqRMState' = [rm \in PROCS |-> "working"]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << count, relRMState, stack, acquires, available_, 
                            remaining_, retVal_, releases, available, 
                            remaining, retVal >>

a2(self) == /\ pc[self] = "a2"
            /\ retVal_' = [retVal_ EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, releases, available, 
                            remaining, retVal >>

a3(self) == /\ pc[self] = "a3"
            /\ IF count = available_[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "a4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

a4(self) == /\ pc[self] = "a4"
            /\ retVal_' = [retVal_ EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, releases, available, 
                            remaining, retVal >>

a5(self) == /\ pc[self] = "a5"
            /\ IF retVal_[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "ac"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

ac(self) == /\ pc[self] = "ac"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "commit_acquire_transaction",
                                                     pc        |->  "a6" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "tca"]
            /\ UNCHANGED << count, acqRMState, relRMState, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

a6(self) == /\ pc[self] = "a6"
            /\ IF acqRMState[self] = "commited"
                  THEN /\ count' = remaining_[self]
                       /\ pc' = [pc EXCEPT ![self] = "a7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a1"]
                       /\ count' = count
            /\ UNCHANGED << acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

a7(self) == /\ pc[self] = "a7"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ retVal_' = [retVal_ EXCEPT ![self] = Head(stack[self]).retVal_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, acqRMState, relRMState, releases, available, 
                            remaining, retVal >>

acquire(self) == a1(self) \/ as(self) \/ a2(self) \/ a3(self) \/ a4(self)
                    \/ a5(self) \/ ac(self) \/ a6(self) \/ a7(self)

r1(self) == /\ pc[self] = "r1"
            /\ available' = [available EXCEPT ![self] = count]
            /\ remaining' = [remaining EXCEPT ![self] = available'[self] + releases[self]]
            /\ pc' = [pc EXCEPT ![self] = "rs"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, retVal >>

rs(self) == /\ pc[self] = "rs"
            /\ relRMState' = [rm \in PROCS |-> "working"]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << count, acqRMState, stack, acquires, available_, 
                            remaining_, retVal_, releases, available, 
                            remaining, retVal >>

r2(self) == /\ pc[self] = "r2"
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "r3"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining >>

r3(self) == /\ pc[self] = "r3"
            /\ IF count = available[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "r4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r5"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

r4(self) == /\ pc[self] = "r4"
            /\ retVal' = [retVal EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "r5"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining >>

r5(self) == /\ pc[self] = "r5"
            /\ IF retVal[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "rc"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r1"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

rc(self) == /\ pc[self] = "rc"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "commit_release_transaction",
                                                     pc        |->  "r6" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "tcr"]
            /\ UNCHANGED << count, acqRMState, relRMState, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

r6(self) == /\ pc[self] = "r6"
            /\ IF relRMState[self] = "commited"
                  THEN /\ count' = remaining[self]
                       /\ pc' = [pc EXCEPT ![self] = "r7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r1"]
                       /\ count' = count
            /\ UNCHANGED << acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

r7(self) == /\ pc[self] = "r7"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, acqRMState, relRMState, acquires, 
                            available_, remaining_, retVal_ >>

release(self) == r1(self) \/ rs(self) \/ r2(self) \/ r3(self) \/ r4(self)
                    \/ r5(self) \/ rc(self) \/ r6(self) \/ r7(self)

u1(self) == /\ pc[self] = "u1"
            /\ /\ acquires' = [acquires EXCEPT ![self] = NUM_OF_PERMITS]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire",
                                                        pc        |->  "u2",
                                                        available_ |->  available_[self],
                                                        remaining_ |->  remaining_[self],
                                                        retVal_   |->  retVal_[self],
                                                        acquires  |->  acquires[self] ] >>
                                                    \o stack[self]]
            /\ available_' = [available_ EXCEPT ![self] = defaultInitValue]
            /\ remaining_' = [remaining_ EXCEPT ![self] = defaultInitValue]
            /\ retVal_' = [retVal_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << count, acqRMState, relRMState, releases, available, 
                            remaining, retVal >>

u2(self) == /\ pc[self] = "u2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, acqRMState, relRMState, stack, acquires, 
                            available_, remaining_, retVal_, releases, 
                            available, remaining, retVal >>

u3(self) == /\ pc[self] = "u3"
            /\ /\ releases' = [releases EXCEPT ![self] = NUM_OF_PERMITS]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release",
                                                        pc        |->  "u1",
                                                        available |->  available[self],
                                                        remaining |->  remaining[self],
                                                        retVal    |->  retVal[self],
                                                        releases  |->  releases[self] ] >>
                                                    \o stack[self]]
            /\ available' = [available EXCEPT ![self] = defaultInitValue]
            /\ remaining' = [remaining EXCEPT ![self] = defaultInitValue]
            /\ retVal' = [retVal EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "r1"]
            /\ UNCHANGED << count, acqRMState, relRMState, acquires, 
                            available_, remaining_, retVal_ >>

proc(self) == u1(self) \/ u2(self) \/ u3(self)

Next == (\E self \in ProcSet:  \/ commit_acquire_transaction(self)
                               \/ commit_release_transaction(self)
                               \/ acquire(self) \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Tue May 19 15:30:20 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
