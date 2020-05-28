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
    lock = [p \in PROCS |-> 0];
    
define {
    TypeInv == count \in 0..SEMAFORE_CAPACITY
    ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY
                                         
    LockAvailable(p0) == \A p \in PROCS : \/ p = p0
                                      \/ lock[p] = 0
}

macro start_transaction()
{
       await LockAvailable(self);
       lock[self] := 1;
}

macro commit_transaction()
{
      lock := [p \in PROCS |-> 0];
}

procedure set_state(available, remaining)

variables 
    retVal = FALSE;
    valCount;
{
ts:        start_transaction();

l1:        valCount := count;
       

s1:        if (valCount = available) {
               retVal := TRUE
           };
                  
s2:        if (retVal) { 

s3:            valCount := remaining;
                
l2:            count := val_count;

tc:            commit_transaction();   

s4:            return;                                                                   
           }
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

r3:        return;               
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
\* Procedure variable available of procedure acquire at line 68 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 69 col 5 changed to remaining_
\* Procedure variable available of procedure release at line 87 col 5 changed to available_r
\* Procedure variable remaining of procedure release at line 88 col 5 changed to remaining_r
CONSTANT defaultInitValue
VARIABLES count, lock, pc, stack

(* define statement *)
TypeInv == count \in 0..SEMAFORE_CAPACITY
ExcInv == Cardinality({p \in PROCS: pc[p] = "u2"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY

LockAvailable(p0) == \A p \in PROCS : \/ p = p0
                                  \/ lock[p] = 0

VARIABLES available, remaining, retVal, val_count, acquires, available_, 
          remaining_, releases, available_r, remaining_r

vars == << count, lock, pc, stack, available, remaining, retVal, val_count, 
           acquires, available_, remaining_, releases, available_r, 
           remaining_r >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = SEMAFORE_CAPACITY
        /\ lock = [p \in PROCS |-> 0]
        (* Procedure set_state *)
        /\ available = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal = [ self \in ProcSet |-> FALSE]
        /\ val_count = [ self \in ProcSet |-> defaultInitValue]
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

ts(self) == /\ pc[self] = "ts"
            /\ LockAvailable(self)
            /\ lock' = [lock EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << count, stack, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

l1(self) == /\ pc[self] = "l1"
            /\ val_count' = [val_count EXCEPT ![self] = count]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << count, lock, stack, available, remaining, retVal, 
                            acquires, available_, remaining_, releases, 
                            available_r, remaining_r >>

s1(self) == /\ pc[self] = "s1"
            /\ IF val_count[self] = available[self]
                  THEN /\ retVal' = [retVal EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << count, lock, stack, available, remaining, 
                            val_count, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

s2(self) == /\ pc[self] = "s2"
            /\ IF retVal[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "s3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << count, lock, stack, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

s3(self) == /\ pc[self] = "s3"
            /\ val_count' = [val_count EXCEPT ![self] = remaining[self]]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << count, lock, stack, available, remaining, retVal, 
                            acquires, available_, remaining_, releases, 
                            available_r, remaining_r >>

l2(self) == /\ pc[self] = "l2"
            /\ count' = val_count[self]
            /\ pc' = [pc EXCEPT ![self] = "tc"]
            /\ UNCHANGED << lock, stack, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

tc(self) == /\ pc[self] = "tc"
            /\ lock' = [p \in PROCS |-> 0]
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << count, stack, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

s4(self) == /\ pc[self] = "s4"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ val_count' = [val_count EXCEPT ![self] = Head(stack[self]).val_count]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

set_state(self) == ts(self) \/ l1(self) \/ s1(self) \/ s2(self) \/ s3(self)
                      \/ l2(self) \/ tc(self) \/ s4(self)

a1(self) == /\ pc[self] = "a1"
            /\ available_' = [available_ EXCEPT ![self] = count]
            /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << count, lock, stack, available, remaining, retVal, 
                            val_count, acquires, releases, available_r, 
                            remaining_r >>

a2(self) == /\ pc[self] = "a2"
            /\ remaining_[self] >= 0
            /\ /\ available' = [available EXCEPT ![self] = available_[self]]
               /\ remaining' = [remaining EXCEPT ![self] = remaining_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_state",
                                                        pc        |->  "a3",
                                                        retVal    |->  retVal[self],
                                                        val_count |->  val_count[self],
                                                        available |->  available[self],
                                                        remaining |->  remaining[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ val_count' = [val_count EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, lock, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

a3(self) == /\ pc[self] = "a3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, available, remaining, retVal, 
                            val_count, releases, available_r, remaining_r >>

acquire(self) == a1(self) \/ a2(self) \/ a3(self)

r1(self) == /\ pc[self] = "r1"
            /\ available_r' = [available_r EXCEPT ![self] = count]
            /\ remaining_r' = [remaining_r EXCEPT ![self] = available_r'[self] + releases[self]]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << count, lock, stack, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_, 
                            releases >>

r2(self) == /\ pc[self] = "r2"
            /\ /\ available' = [available EXCEPT ![self] = available_r[self]]
               /\ remaining' = [remaining EXCEPT ![self] = remaining_r[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_state",
                                                        pc        |->  "r3",
                                                        retVal    |->  retVal[self],
                                                        val_count |->  val_count[self],
                                                        available |->  available[self],
                                                        remaining |->  remaining[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ val_count' = [val_count EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, lock, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

r3(self) == /\ pc[self] = "r3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_r' = [available_r EXCEPT ![self] = Head(stack[self]).available_r]
            /\ remaining_r' = [remaining_r EXCEPT ![self] = Head(stack[self]).remaining_r]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_ >>

release(self) == r1(self) \/ r2(self) \/ r3(self)

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
            /\ UNCHANGED << count, lock, available, remaining, retVal, 
                            val_count, releases, available_r, remaining_r >>

u2(self) == /\ pc[self] = "u2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, lock, stack, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

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
            /\ UNCHANGED << count, lock, available, remaining, retVal, 
                            val_count, acquires, available_, remaining_ >>

proc(self) == u1(self) \/ u2(self) \/ u3(self)

Next == (\E self \in ProcSet:  \/ set_state(self) \/ acquire(self)
                               \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Thu May 28 17:42:03 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
