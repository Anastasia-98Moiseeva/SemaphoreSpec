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
    txStatus = [p \in PROCS |-> "none"];
    opIndicator = [p \in PROCS |-> "none"];
    
define {

    TypeInv == count \in 0..SEMAFORE_CAPACITY
    
    ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY
    
    PermitInv == Cardinality({p \in PROCS: \/ pc[p] = "cs"
                                           \/ /\ pc[p] \in {"l2", "s5", "a1", "a4"}
                                              /\ opIndicator[p] = "acquire" 
                                              /\ succeedOp[p] 
                                          \/ pc[p] = "u3"                
                                          \/ /\ pc[p] \in {"r1", "r2", "ts", "l1", "s1", "s2", "s3", "s4", "tc", "l2", "s5"}
                                             /\ opIndicator[p] = "release"
                                             /\ succeedOp[p] = FALSE }) * NUM_OF_PERMITS + count = SEMAFORE_CAPACITY

    
    TxInv == \A p \in PROCS : txStatus[p] \in {"none", "started", "committed", "aborted"}
                                            
    LocksNotExist == \A p \in PROCS : lock[p] = 0
    
    CommitAvailable == \A p \in PROCS : \/ txStatus[p] = "none"
                                        \/ txStatus[p] = "started"                                                               
}

macro start_transaction(p)
{
      txStatus[p] := "started";      
}

macro commit_transaction(p, valCount)
{
      if (CommitAvailable) {
           count := valCount;
           succeedOp[self] := TRUE;
           txStatus[p] := "committed";
      } else {
           txStatus[p] := "aborted";
      }
}

procedure compare_and_set_state(expVal, newVal)

variables 
    retVal = FALSE;
    valCount;
{
ts:        start_transaction(self);

l1:        lock[self] := 1;

s1:        valCount := count;
       

s2:        if (valCount = expVal) {
               retVal := TRUE
           };
                  
s3:        if (retVal) { 

s4:            valCount := newVal;

tc:            commit_transaction(self, valCount);
                                                                           
           };

l2:        lock[self] := 0;
           
s5:        await LocksNotExist;
           txStatus[self] := "none";

           return; 
}

procedure acquire(acquires)

variables 
    available;
    remaining;  
{    
a1:    while (succeedOp[self] = FALSE) {

           available := count;
           remaining := available - acquires;  
                    
a2:        await remaining >= 0;  
           call compare_and_set_state(available, remaining)       
       };
       
a4:    succeedOp[self] := FALSE;
       return;      
}

procedure release(releases)

variables 
    available;
    remaining;
{     
r1:    while (succeedOp[self] = FALSE) { 

           available := count;
           remaining := available + releases;
           
r2:        call compare_and_set_state(available, remaining)
       };
       
r3:    succeedOp[self] := FALSE;
       return;
}

process (proc \in PROCS)
    {
u1:   while (TRUE) {

u2:         opIndicator[self] := "acquire";
            call acquire(NUM_OF_PERMITS);            
cs:         skip;
u3:         opIndicator[self] := "release";
            call release(NUM_OF_PERMITS);
      }
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATIONNUMberNUMberNUMber
\* Procedure variable available of procedure acquire at line 98 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 99 col 5 changed to remaining_
CONSTANT defaultInitValue
VARIABLES count, lock, succeedOp, txStatus, opIndicator, pc, stack

(* define statement *)
TypeInv == count \in 0..SEMAFORE_CAPACITY

ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY

PermitInv == Cardinality({p \in PROCS: \/ pc[p] = "cs"
                                       \/ /\ pc[p] \in {"l2", "s5", "a1", "a4"}
                                          /\ opIndicator[p] = "acquire"
                                          /\ succeedOp[p]
                                      \/ pc[p] = "u3"
                                      \/ /\ pc[p] \in {"r1", "r2", "ts", "l1", "s1", "s2", "s3", "s4", "tc", "l2", "s5"}
                                         /\ opIndicator[p] = "release"
                                         /\ succeedOp[p] = FALSE }) * NUM_OF_PERMITS + count = SEMAFORE_CAPACITY


TxInv == \A p \in PROCS : txStatus[p] \in {"none", "started", "committed", "aborted"}

LocksNotExist == \A p \in PROCS : lock[p] = 0

CommitAvailable == \A p \in PROCS : \/ txStatus[p] = "none"
                                    \/ txStatus[p] = "started"

VARIABLES expVal, newVal, retVal, valCount, acquires, available_, remaining_, 
          releases, available, remaining

vars == << count, lock, succeedOp, txStatus, opIndicator, pc, stack, expVal, 
           newVal, retVal, valCount, acquires, available_, remaining_, 
           releases, available, remaining >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = SEMAFORE_CAPACITY
        /\ lock = [p \in PROCS |-> 0]
        /\ succeedOp = [p \in PROCS |-> FALSE]
        /\ txStatus = [p \in PROCS |-> "none"]
        /\ opIndicator = [p \in PROCS |-> "none"]
        (* Procedure compare_and_set_state *)
        /\ expVal = [ self \in ProcSet |-> defaultInitValue]
        /\ newVal = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal = [ self \in ProcSet |-> FALSE]
        /\ valCount = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure acquire *)
        /\ acquires = [ self \in ProcSet |-> defaultInitValue]
        /\ available_ = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure release *)
        /\ releases = [ self \in ProcSet |-> defaultInitValue]
        /\ available = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "u1"]

ts(self) == /\ pc[self] = "ts"
            /\ txStatus' = [txStatus EXCEPT ![self] = "started"]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << count, lock, succeedOp, opIndicator, stack, expVal, 
                            newVal, retVal, valCount, acquires, available_, 
                            remaining_, releases, available, remaining >>

l1(self) == /\ pc[self] = "l1"
            /\ lock' = [lock EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s1(self) == /\ pc[self] = "s1"
            /\ valCount' = [valCount EXCEPT ![self] = count]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, retVal, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s2(self) == /\ pc[self] = "s2"
            /\ IF valCount[self] = expVal[self]
                  THEN /\ retVal' = [retVal EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s3(self) == /\ pc[self] = "s3"
            /\ IF retVal[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "s4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s4(self) == /\ pc[self] = "s4"
            /\ valCount' = [valCount EXCEPT ![self] = newVal[self]]
            /\ pc' = [pc EXCEPT ![self] = "tc"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, retVal, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

tc(self) == /\ pc[self] = "tc"
            /\ IF CommitAvailable
                  THEN /\ count' = valCount[self]
                       /\ succeedOp' = [succeedOp EXCEPT ![self] = TRUE]
                       /\ txStatus' = [txStatus EXCEPT ![self] = "committed"]
                  ELSE /\ txStatus' = [txStatus EXCEPT ![self] = "aborted"]
                       /\ UNCHANGED << count, succeedOp >>
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << lock, opIndicator, stack, expVal, newVal, retVal, 
                            valCount, acquires, available_, remaining_, 
                            releases, available, remaining >>

l2(self) == /\ pc[self] = "l2"
            /\ lock' = [lock EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s5(self) == /\ pc[self] = "s5"
            /\ LocksNotExist
            /\ txStatus' = [txStatus EXCEPT ![self] = "none"]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ valCount' = [valCount EXCEPT ![self] = Head(stack[self]).valCount]
            /\ expVal' = [expVal EXCEPT ![self] = Head(stack[self]).expVal]
            /\ newVal' = [newVal EXCEPT ![self] = Head(stack[self]).newVal]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, succeedOp, opIndicator, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

compare_and_set_state(self) == ts(self) \/ l1(self) \/ s1(self) \/ s2(self)
                                  \/ s3(self) \/ s4(self) \/ tc(self)
                                  \/ l2(self) \/ s5(self)

a1(self) == /\ pc[self] = "a1"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ available_' = [available_ EXCEPT ![self] = count]
                       /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
                       /\ pc' = [pc EXCEPT ![self] = "a2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a4"]
                       /\ UNCHANGED << available_, remaining_ >>
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            releases, available, remaining >>

a2(self) == /\ pc[self] = "a2"
            /\ remaining_[self] >= 0
            /\ /\ expVal' = [expVal EXCEPT ![self] = available_[self]]
               /\ newVal' = [newVal EXCEPT ![self] = remaining_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare_and_set_state",
                                                        pc        |->  "a1",
                                                        retVal    |->  retVal[self],
                                                        valCount  |->  valCount[self],
                                                        expVal    |->  expVal[self],
                                                        newVal    |->  newVal[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ valCount' = [valCount EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

a4(self) == /\ pc[self] = "a4"
            /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, txStatus, opIndicator, expVal, newVal, 
                            retVal, valCount, releases, available, remaining >>

acquire(self) == a1(self) \/ a2(self) \/ a4(self)

r1(self) == /\ pc[self] = "r1"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ available' = [available EXCEPT ![self] = count]
                       /\ remaining' = [remaining EXCEPT ![self] = available'[self] + releases[self]]
                       /\ pc' = [pc EXCEPT ![self] = "r2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r3"]
                       /\ UNCHANGED << available, remaining >>
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases >>

r2(self) == /\ pc[self] = "r2"
            /\ /\ expVal' = [expVal EXCEPT ![self] = available[self]]
               /\ newVal' = [newVal EXCEPT ![self] = remaining[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare_and_set_state",
                                                        pc        |->  "r1",
                                                        retVal    |->  retVal[self],
                                                        valCount  |->  valCount[self],
                                                        expVal    |->  expVal[self],
                                                        newVal    |->  newVal[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ valCount' = [valCount EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

r3(self) == /\ pc[self] = "r3"
            /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, lock, txStatus, opIndicator, expVal, newVal, 
                            retVal, valCount, acquires, available_, remaining_ >>

release(self) == r1(self) \/ r2(self) \/ r3(self)

u1(self) == /\ pc[self] = "u1"
            /\ pc' = [pc EXCEPT ![self] = "u2"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

u2(self) == /\ pc[self] = "u2"
            /\ opIndicator' = [opIndicator EXCEPT ![self] = "acquire"]
            /\ /\ acquires' = [acquires EXCEPT ![self] = NUM_OF_PERMITS]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire",
                                                        pc        |->  "cs",
                                                        available_ |->  available_[self],
                                                        remaining_ |->  remaining_[self],
                                                        acquires  |->  acquires[self] ] >>
                                                    \o stack[self]]
            /\ available_' = [available_ EXCEPT ![self] = defaultInitValue]
            /\ remaining_' = [remaining_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, expVal, newVal, 
                            retVal, valCount, releases, available, remaining >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, opIndicator, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

u3(self) == /\ pc[self] = "u3"
            /\ opIndicator' = [opIndicator EXCEPT ![self] = "release"]
            /\ /\ releases' = [releases EXCEPT ![self] = NUM_OF_PERMITS]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release",
                                                        pc        |->  "u1",
                                                        available |->  available[self],
                                                        remaining |->  remaining[self],
                                                        releases  |->  releases[self] ] >>
                                                    \o stack[self]]
            /\ available' = [available EXCEPT ![self] = defaultInitValue]
            /\ remaining' = [remaining EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "r1"]
            /\ UNCHANGED << count, lock, succeedOp, txStatus, expVal, newVal, 
                            retVal, valCount, acquires, available_, remaining_ >>

proc(self) == u1(self) \/ u2(self) \/ cs(self) \/ u3(self)

Next == (\E self \in ProcSet:  \/ compare_and_set_state(self)
                               \/ acquire(self) \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Jun 19 02:20:03 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
