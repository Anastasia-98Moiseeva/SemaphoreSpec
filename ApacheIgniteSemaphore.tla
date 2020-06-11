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
    succeedOp = [p \in PROCS |-> FALSE];
    txStatus = "none";
    
define {

    TypeInv == count \in 0..SEMAFORE_CAPACITY
    
    ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY
    
    TxInv == txStatus \in {"none", "started", "committed", "aborted"}
                                            
    LocksNotExist == \A p \in PROCS : lock[p] = 0                              
                                                
}

macro start_transaction()
{
      lock[self] := 1;
      txStatus := "started";
}

macro commit_transaction(valCount)
{
      if (txStatus = "started") {
           count := valCount;
           succeedOp[self] := TRUE;
           txStatus := "committed";
      }
}

procedure set_state(available, remaining)

variables 
    retVal = FALSE;
    valCount;
{
ts:        start_transaction();

s1:        valCount := count;
       

s2:        if (valCount = available) {
               retVal := TRUE
           };
                  
s3:        if (retVal) { 

s4:            valCount := remaining;

tc:            commit_transaction(valCount);
                                                                           
           };

s5:        lock[self] := 0;
           
s6:        await LocksNotExist;
           txStatus := "none";

           return; 
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
           
a4:        return 
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
           
r3:        return 
       };
}

process (proc \in PROCS)
    {
u1:   while (TRUE) {

u2:         while (succeedOp[self] = FALSE) { 
                call acquire(NUM_OF_PERMITS)
            };
            succeedOp[self] := FALSE;
            
cs:         skip;

u3:         while (succeedOp[self] = FALSE) { 
                call release(NUM_OF_PERMITS);
            };
            succeedOp[self] := FALSE;
      }
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATIONNUMberNUMberNUMber
\* Procedure variable available of procedure acquire at line 82 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 83 col 5 changed to remaining_
\* Procedure variable available of procedure release at line 100 col 5 changed to available_r
\* Procedure variable remaining of procedure release at line 101 col 5 changed to remaining_r
CONSTANT defaultInitValue
VARIABLES count, lock, succeedOp, txStatus, pc, stack

(* define statement *)
TypeInv == count \in 0..SEMAFORE_CAPACITY

ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY

TxInv == txStatus \in {"none", "started", "committed", "aborted"}

LocksNotExist == \A p \in PROCS : lock[p] = 0

VARIABLES available, remaining, retVal, valCount, acquires, available_, 
          remaining_, releases, available_r, remaining_r

vars == << count, lock, succeedOp, txStatus, pc, stack, available, remaining, 
           retVal, valCount, acquires, available_, remaining_, releases, 
           available_r, remaining_r >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = SEMAFORE_CAPACITY
        /\ lock = [p \in PROCS |-> 0]
        /\ succeedOp = [p \in PROCS |-> FALSE]
        /\ txStatus = "none"
        (* Procedure set_state *)
        /\ available = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal = [ self \in ProcSet |-> FALSE]
        /\ valCount = [ self \in ProcSet |-> defaultInitValue]
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
            /\ lock' = [lock EXCEPT ![self] = 1]
            /\ txStatus' = "started"
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << count, succeedOp, stack, available, remaining, 
                            retVal, valCount, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

s1(self) == /\ pc[self] = "s1"
            /\ valCount' = [valCount EXCEPT ![self] = count]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, retVal, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

s2(self) == /\ pc[self] = "s2"
            /\ IF valCount[self] = available[self]
                  THEN /\ retVal' = [retVal EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, valCount, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

s3(self) == /\ pc[self] = "s3"
            /\ IF retVal[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "s4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, retVal, valCount, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

s4(self) == /\ pc[self] = "s4"
            /\ valCount' = [valCount EXCEPT ![self] = remaining[self]]
            /\ pc' = [pc EXCEPT ![self] = "tc"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, retVal, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

tc(self) == /\ pc[self] = "tc"
            /\ IF txStatus = "started"
                  THEN /\ count' = valCount[self]
                       /\ succeedOp' = [succeedOp EXCEPT ![self] = TRUE]
                       /\ txStatus' = "committed"
                  ELSE /\ TRUE
                       /\ UNCHANGED << count, succeedOp, txStatus >>
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << lock, stack, available, remaining, retVal, 
                            valCount, acquires, available_, remaining_, 
                            releases, available_r, remaining_r >>

s5(self) == /\ pc[self] = "s5"
            /\ lock' = [lock EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "s6"]
            /\ UNCHANGED << count, succeedOp, txStatus, stack, available, 
                            remaining, retVal, valCount, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

s6(self) == /\ pc[self] = "s6"
            /\ LocksNotExist
            /\ txStatus' = "none"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ valCount' = [valCount EXCEPT ![self] = Head(stack[self]).valCount]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, succeedOp, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

set_state(self) == ts(self) \/ s1(self) \/ s2(self) \/ s3(self) \/ s4(self)
                      \/ tc(self) \/ s5(self) \/ s6(self)

a1(self) == /\ pc[self] = "a1"
            /\ available_' = [available_ EXCEPT ![self] = count]
            /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, retVal, valCount, acquires, releases, 
                            available_r, remaining_r >>

a2(self) == /\ pc[self] = "a2"
            /\ remaining_[self] >= 0
            /\ /\ available' = [available EXCEPT ![self] = available_[self]]
               /\ remaining' = [remaining EXCEPT ![self] = remaining_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_state",
                                                        pc        |->  "a4",
                                                        retVal    |->  retVal[self],
                                                        valCount  |->  valCount[self],
                                                        available |->  available[self],
                                                        remaining |->  remaining[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ valCount' = [valCount EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, acquires, 
                            available_, remaining_, releases, available_r, 
                            remaining_r >>

a4(self) == /\ pc[self] = "a4"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, available, 
                            remaining, retVal, valCount, releases, available_r, 
                            remaining_r >>

acquire(self) == a1(self) \/ a2(self) \/ a4(self)

r1(self) == /\ pc[self] = "r1"
            /\ available_r' = [available_r EXCEPT ![self] = count]
            /\ remaining_r' = [remaining_r EXCEPT ![self] = available_r'[self] + releases[self]]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, retVal, valCount, acquires, available_, 
                            remaining_, releases >>

r2(self) == /\ pc[self] = "r2"
            /\ /\ available' = [available EXCEPT ![self] = available_r[self]]
               /\ remaining' = [remaining EXCEPT ![self] = remaining_r[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_state",
                                                        pc        |->  "r3",
                                                        retVal    |->  retVal[self],
                                                        valCount  |->  valCount[self],
                                                        available |->  available[self],
                                                        remaining |->  remaining[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ valCount' = [valCount EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, acquires, 
                            available_, remaining_, releases, available_r, 
                            remaining_r >>

r3(self) == /\ pc[self] = "r3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_r' = [available_r EXCEPT ![self] = Head(stack[self]).available_r]
            /\ remaining_r' = [remaining_r EXCEPT ![self] = Head(stack[self]).remaining_r]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, available, 
                            remaining, retVal, valCount, acquires, available_, 
                            remaining_ >>

release(self) == r1(self) \/ r2(self) \/ r3(self)

u1(self) == /\ pc[self] = "u1"
            /\ pc' = [pc EXCEPT ![self] = "u2"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, retVal, valCount, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

u2(self) == /\ pc[self] = "u2"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ /\ acquires' = [acquires EXCEPT ![self] = NUM_OF_PERMITS]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire",
                                                                   pc        |->  "u2",
                                                                   available_ |->  available_[self],
                                                                   remaining_ |->  remaining_[self],
                                                                   acquires  |->  acquires[self] ] >>
                                                               \o stack[self]]
                       /\ available_' = [available_ EXCEPT ![self] = defaultInitValue]
                       /\ remaining_' = [remaining_ EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "a1"]
                       /\ UNCHANGED succeedOp
                  ELSE /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << stack, acquires, available_, remaining_ >>
            /\ UNCHANGED << count, lock, txStatus, available, remaining, 
                            retVal, valCount, releases, available_r, 
                            remaining_r >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, stack, available, 
                            remaining, retVal, valCount, acquires, available_, 
                            remaining_, releases, available_r, remaining_r >>

u3(self) == /\ pc[self] = "u3"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ /\ releases' = [releases EXCEPT ![self] = NUM_OF_PERMITS]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release",
                                                                   pc        |->  "u3",
                                                                   available_r |->  available_r[self],
                                                                   remaining_r |->  remaining_r[self],
                                                                   releases  |->  releases[self] ] >>
                                                               \o stack[self]]
                       /\ available_r' = [available_r EXCEPT ![self] = defaultInitValue]
                       /\ remaining_r' = [remaining_r EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "r1"]
                       /\ UNCHANGED succeedOp
                  ELSE /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "u1"]
                       /\ UNCHANGED << stack, releases, available_r, 
                                       remaining_r >>
            /\ UNCHANGED << count, lock, txStatus, available, remaining, 
                            retVal, valCount, acquires, available_, remaining_ >>

proc(self) == u1(self) \/ u2(self) \/ cs(self) \/ u3(self)

Next == (\E self \in ProcSet:  \/ set_state(self) \/ acquire(self)
                               \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Jun 12 02:46:04 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
