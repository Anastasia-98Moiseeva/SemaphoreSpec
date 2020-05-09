----------------------- MODULE ApacheIgniteSemaphore -----------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS PROCS,
          MAXVAL,     
          NUM,          \* the number of threads that can capture the semaphore
          PERMITS
          
ASSUME /\ MAXVAL \in Nat\{0}
       /\ Cardinality(PROCS) <= MAXVAL + 1
       /\ NUM \in Nat\{0}
       /\ PERMITS \in Nat\{0}

(***************************************************************************
--algorithm GridCacheSemaphoreImpl {

variables
    count = NUM;
    
define {
    TypeInv == count \in 0..NUM
    ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) <= NUM
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
                     
           retVal := FALSE;
a2:        if (count = available) {
               retVal := TRUE
           };
                  
           if (retVal) {  
                   
               count := remaining;
               
a3:            return
               
           };     
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
                       
           retVal := FALSE;
r2:        if (count = available) {
               retVal := TRUE
           };      
           
           if (retVal) {
                     
               count := remaining;   
                         
r3:            return
           };            
       } 
}

process (proc \in PROCS)
    {
u1:   while (TRUE) {
            call acquire(PERMITS);
u2:         skip;
u3:         call release(PERMITS);
      }
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATIONNUMberNUMberNUMber
\* Procedure variable available of procedure acquire at line 28 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 29 col 5 changed to remaining_
\* Procedure variable retVal of procedure acquire at line 30 col 5 changed to retVal_
CONSTANT defaultInitValue
VARIABLES count, pc, stack

(* define statement *)
TypeInv == count \in 0..NUM
ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) <= NUM

VARIABLES acquires, available_, remaining_, retVal_, releases, available, 
          remaining, retVal

vars == << count, pc, stack, acquires, available_, remaining_, retVal_, 
           releases, available, remaining, retVal >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = NUM
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

a1(self) == /\ pc[self] = "a1"
            /\ available_' = [available_ EXCEPT ![self] = count]
            /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
            /\ remaining_'[self] >= 0
            /\ retVal_' = [retVal_ EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << count, stack, acquires, releases, available, 
                            remaining, retVal >>

a2(self) == /\ pc[self] = "a2"
            /\ IF count = available_[self]
                  THEN /\ retVal_' = [retVal_ EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal_
            /\ IF retVal_'[self]
                  THEN /\ count' = remaining_[self]
                       /\ pc' = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a1"]
                       /\ count' = count
            /\ UNCHANGED << stack, acquires, available_, remaining_, releases, 
                            available, remaining, retVal >>

a3(self) == /\ pc[self] = "a3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ retVal_' = [retVal_ EXCEPT ![self] = Head(stack[self]).retVal_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, releases, available, remaining, retVal >>

acquire(self) == a1(self) \/ a2(self) \/ a3(self)

r1(self) == /\ pc[self] = "r1"
            /\ available' = [available EXCEPT ![self] = count]
            /\ remaining' = [remaining EXCEPT ![self] = available'[self] + releases[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << count, stack, acquires, available_, remaining_, 
                            retVal_, releases >>

r2(self) == /\ pc[self] = "r2"
            /\ IF count = available[self]
                  THEN /\ retVal' = [retVal EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal
            /\ IF retVal'[self]
                  THEN /\ count' = remaining[self]
                       /\ pc' = [pc EXCEPT ![self] = "r3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r1"]
                       /\ count' = count
            /\ UNCHANGED << stack, acquires, available_, remaining_, retVal_, 
                            releases, available, remaining >>

r3(self) == /\ pc[self] = "r3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, acquires, available_, remaining_, retVal_ >>

release(self) == r1(self) \/ r2(self) \/ r3(self)

u1(self) == /\ pc[self] = "u1"
            /\ /\ acquires' = [acquires EXCEPT ![self] = PERMITS]
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
            /\ UNCHANGED << count, releases, available, remaining, retVal >>

u2(self) == /\ pc[self] = "u2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, stack, acquires, available_, remaining_, 
                            retVal_, releases, available, remaining, retVal >>

u3(self) == /\ pc[self] = "u3"
            /\ /\ releases' = [releases EXCEPT ![self] = PERMITS]
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
            /\ UNCHANGED << count, acquires, available_, remaining_, retVal_ >>

proc(self) == u1(self) \/ u2(self) \/ u3(self)

Next == (\E self \in ProcSet: acquire(self) \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Sat May 09 04:55:59 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
