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
    available_permits = SEMAFORE_CAPACITY;
    
    acqRMState = [rm \in PROCS |-> "not init"];
    relRMState = [rm \in PROCS |-> "not init"];  
    
define {
    TypeInv == count \in 0..SEMAFORE_CAPACITY
    ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY
    \*PermitInv == available + Cardinality({p \in PROCS: pc[p] = "u2"}) * NUM_OF_PERMITS= SEMAFORE_CAPACITY
       
    (* 
    TCTypeInv == \A rm \in PROCS : /\ acqRMState[rm] \in {"not init", "working", "prepared", "commited", "aborted"}
                                   /\ relRMState[rm] \in {"not init", "working", "prepared", "commited", "aborted"}
                                                       
    TCConsistentInv == \A rm1, rm2 \in PROCS : /\ ~ /\ acqRMState[rm1] = "aborted"
                                                    /\ acqRMState[rm2] = "committed"                      
                                               /\ ~ /\ relRMState[rm1] = "aborted"
                                                    /\ relRMState[rm2] = "committed"
    
    CanCommit(rmState) == \A rm \in PROCS : rmState[rm] \in {"prepared", "committed"}
    NotCommitted(rmState) == \A rm \in PROCS : rmState[rm] # "committed" 
    *)
}
(*
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
*)

procedure set_state(available, remaining)

variables 
    retVal = FALSE;
{
s1:        if (count = available) {
               retVal := TRUE
           };
                  
           if (retVal) {                    
               count := remaining;                    
s2:            return
           }; 
}

procedure acquire(acquires)

variables 
    available;
    remaining; 
    
{    
a1:    while (TRUE) {

           available := count;
           remaining := available - acquires;  
                    
a2:        await remaining >= 0;                                 
           call set_state(available, remaining);      
                       
a3:        return 
       };
}

procedure release(releases)

variables 
    available;
    remaining;
    
{     
r1:    while (TRUE) {

           available := count;
           remaining := available + releases;
           
r2:        call set_state(available, remaining);

a3:        return;               
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
\* Label a3 of procedure acquire at line 114 col 12 changed to a3_
\* Procedure variable available of procedure acquire at line 102 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 103 col 5 changed to remaining_
\* Procedure variable available of procedure release at line 121 col 5 changed to available_r
\* Procedure variable remaining of procedure release at line 122 col 5 changed to remaining_r
CONSTANT defaultInitValue
VARIABLES count, available_permits, acqRMState, relRMState, pc, stack

(* define statement *)
TypeInv == count \in 0..SEMAFORE_CAPACITY
ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY

VARIABLES available, remaining, retVal, acquires, available_, remaining_, 
          releases, available_r, remaining_r

vars == << count, available_permits, acqRMState, relRMState, pc, stack, 
           available, remaining, retVal, acquires, available_, remaining_, 
           releases, available_r, remaining_r >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = SEMAFORE_CAPACITY
        /\ available_permits = SEMAFORE_CAPACITY
        /\ acqRMState = [rm \in PROCS |-> "not init"]
        /\ relRMState = [rm \in PROCS |-> "not init"]
        (* Procedure set_state *)
        /\ available = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal = [ self \in ProcSet |-> FALSE]
        (* Procedure acquire *)
        /\ acquires = [ self \in ProcSet |-> defaultInitValue]
        /\ available_ = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure release *)
        /\ releases = [ self \in ProcSet |-> defaultInitValue]
        /\ available_r = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining_r = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "u1"]

s1(self) == /\ pc[self] = "s1"
            /\ IF count = available[self]
                  THEN /\ retVal' = [retVal EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal
            /\ IF retVal'[self]
                  THEN /\ count' = remaining[self]
                       /\ pc' = [pc EXCEPT ![self] = "s2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                       /\ count' = count
            /\ UNCHANGED << available_permits, acqRMState, relRMState, stack, 
                            available, remaining, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

s2(self) == /\ pc[self] = "s2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            acquires, available_, remaining_, releases, 
                            available_r, remaining_r >>

set_state(self) == s1(self) \/ s2(self)

a1(self) == /\ pc[self] = "a1"
            /\ available_' = [available_ EXCEPT ![self] = count]
            /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            stack, available, remaining, retVal, acquires, 
                            releases, available_r, remaining_r >>

a2(self) == /\ pc[self] = "a2"
            /\ remaining_[self] >= 0
            /\ /\ available' = [available EXCEPT ![self] = available_[self]]
               /\ remaining' = [remaining EXCEPT ![self] = remaining_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_state",
                                                        pc        |->  "a3_",
                                                        retVal    |->  retVal[self],
                                                        available |->  available[self],
                                                        remaining |->  remaining[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            acquires, available_, remaining_, releases, 
                            available_r, remaining_r >>

a3_(self) == /\ pc[self] = "a3_"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
             /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
             /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                             available, remaining, retVal, releases, 
                             available_r, remaining_r >>

acquire(self) == a1(self) \/ a2(self) \/ a3_(self)

r1(self) == /\ pc[self] = "r1"
            /\ available_r' = [available_r EXCEPT ![self] = count]
            /\ remaining_r' = [remaining_r EXCEPT ![self] = available_r'[self] + releases[self]]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            stack, available, remaining, retVal, acquires, 
                            available_, remaining_, releases >>

r2(self) == /\ pc[self] = "r2"
            /\ /\ available' = [available EXCEPT ![self] = available_r[self]]
               /\ remaining' = [remaining EXCEPT ![self] = remaining_r[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_state",
                                                        pc        |->  "a3",
                                                        retVal    |->  retVal[self],
                                                        available |->  available[self],
                                                        remaining |->  remaining[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            acquires, available_, remaining_, releases, 
                            available_r, remaining_r >>

a3(self) == /\ pc[self] = "a3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_r' = [available_r EXCEPT ![self] = Head(stack[self]).available_r]
            /\ remaining_r' = [remaining_r EXCEPT ![self] = Head(stack[self]).remaining_r]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            available, remaining, retVal, acquires, available_, 
                            remaining_ >>

release(self) == r1(self) \/ r2(self) \/ a3(self)

u1(self) == /\ pc[self] = "u1"
            /\ /\ acquires' = [acquires EXCEPT ![self] = NUM_OF_PERMITS]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire",
                                                        pc        |->  "u2",
                                                        available_ |->  available_[self],
                                                        remaining_ |->  remaining_[self],
                                                        acquires  |->  acquires[self] ] >>
                                                    \o stack[self]]
            /\ available_' = [available_ EXCEPT ![self] = defaultInitValue]
            /\ remaining_' = [remaining_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            available, remaining, retVal, releases, 
                            available_r, remaining_r >>

u2(self) == /\ pc[self] = "u2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            stack, available, remaining, retVal, acquires, 
                            available_, remaining_, releases, available_r, 
                            remaining_r >>

u3(self) == /\ pc[self] = "u3"
            /\ /\ releases' = [releases EXCEPT ![self] = NUM_OF_PERMITS]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release",
                                                        pc        |->  "u1",
                                                        available_r |->  available_r[self],
                                                        remaining_r |->  remaining_r[self],
                                                        releases  |->  releases[self] ] >>
                                                    \o stack[self]]
            /\ available_r' = [available_r EXCEPT ![self] = defaultInitValue]
            /\ remaining_r' = [remaining_r EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "r1"]
            /\ UNCHANGED << count, available_permits, acqRMState, relRMState, 
                            available, remaining, retVal, acquires, available_, 
                            remaining_ >>

proc(self) == u1(self) \/ u2(self) \/ u3(self)

Next == (\E self \in ProcSet:  \/ set_state(self) \/ acquire(self)
                               \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Thu May 21 17:58:05 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
