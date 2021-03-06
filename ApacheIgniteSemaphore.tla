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
    succeedOp = [p \in PROCS |-> TRUE];
    txStatus = [p \in PROCS |-> "none"];
    opIndicator = [p \in PROCS |-> "none"];
    permitNum = [p \in PROCS |-> 0];
    
define {

    TypeInv == /\ count \in 0..SEMAFORE_CAPACITY
               /\ \A p \in PROCS : txStatus[p] \in {"none", "started", "aborted"} 
    
    
    ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY
    
    RECURSIVE Sum(_, _)             
    Sum(S, value) == IF S = {} THEN value
              ELSE LET s == CHOOSE s \in S : TRUE
              IN Sum(S\{s}, value + permitNum[s])
     
    PermitInv == Sum(PROCS, count) = SEMAFORE_CAPACITY
}

macro start_transaction()
{
          txStatus[self] := "started";    
}

macro commit_transaction(valCount)
{
           if (txStatus[self] = "started"){
               count := valCount;
               succeedOp[self] := TRUE;
               txStatus := [[p \in PROCS |-> IF txStatus[p] = "started"
                                            THEN "aborted"
                                            ELSE txStatus[p]]
                                            EXCEPT ![self] = "none"]; 
           } else {
               txStatus[self] := "aborted"
           };
}

macro add_permit_num(p, val)
{
           if (txStatus[self] # "aborted") {
               permitNum[p] := permitNum[p] + val;
           };
}

procedure compare_and_set_state(expVal, newVal)

variables 
    retVal = FALSE;
    valCount;
{
ts:        start_transaction();

           valCount := count;       

s1:        if (valCount = expVal) {
s2:            retVal := TRUE
           };
                  
s3:        if (retVal) { 

s4:            valCount := newVal;

tc:            commit_transaction(valCount);
               add_permit_num(self, expVal - newVal);
           };           
s5:        return; 

}

procedure acquire(acquires)

variables 
    available;
    remaining;  
{    
a1:        succeedOp[self] := FALSE;
a2:        while (succeedOp[self] = FALSE) {

               available := count;
a3:            remaining := available - acquires;  
                    
a4:            if (remaining >= 0) {
                   call compare_and_set_state(available, remaining)
               };     
           };       
a5:        return;      
}

procedure release(releases)

variables 
    available;
    remaining;
{
r1:        succeedOp[self] := FALSE;   
r2:        while (succeedOp[self] = FALSE) { 

               available := count;
r3:            remaining := available + releases;
           
r4:            call compare_and_set_state(available, remaining)
           };       
r5:        return;
}

process (proc \in PROCS)
    {
u1:        while (TRUE) {

u2:            call acquire(NUM_OF_PERMITS);            
cs:            skip;
u3:            call release(NUM_OF_PERMITS);
           }
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATIONNUMberNUMberNUMber
\* Procedure variable available of procedure acquire at line 92 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 93 col 5 changed to remaining_
CONSTANT defaultInitValue
VARIABLES count, succeedOp, txStatus, opIndicator, permitNum, pc, stack

(* define statement *)
TypeInv == /\ count \in 0..SEMAFORE_CAPACITY
           /\ \A p \in PROCS : txStatus[p] \in {"none", "started", "aborted"}


ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY

RECURSIVE Sum(_, _)
Sum(S, value) == IF S = {} THEN value
          ELSE LET s == CHOOSE s \in S : TRUE
          IN Sum(S\{s}, value + permitNum[s])

PermitInv == Sum(PROCS, count) = SEMAFORE_CAPACITY

VARIABLES expVal, newVal, retVal, valCount, acquires, available_, remaining_, 
          releases, available, remaining

vars == << count, succeedOp, txStatus, opIndicator, permitNum, pc, stack, 
           expVal, newVal, retVal, valCount, acquires, available_, remaining_, 
           releases, available, remaining >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = SEMAFORE_CAPACITY
        /\ succeedOp = [p \in PROCS |-> TRUE]
        /\ txStatus = [p \in PROCS |-> "none"]
        /\ opIndicator = [p \in PROCS |-> "none"]
        /\ permitNum = [p \in PROCS |-> 0]
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
            /\ valCount' = [valCount EXCEPT ![self] = count]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << count, succeedOp, opIndicator, permitNum, stack, 
                            expVal, newVal, retVal, acquires, available_, 
                            remaining_, releases, available, remaining >>

s1(self) == /\ pc[self] = "s1"
            /\ IF valCount[self] = expVal[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "s2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s2(self) == /\ pc[self] = "s2"
            /\ retVal' = [retVal EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s3(self) == /\ pc[self] = "s3"
            /\ IF retVal[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "s4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s4(self) == /\ pc[self] = "s4"
            /\ valCount' = [valCount EXCEPT ![self] = newVal[self]]
            /\ pc' = [pc EXCEPT ![self] = "tc"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

tc(self) == /\ pc[self] = "tc"
            /\ IF txStatus[self] = "started"
                  THEN /\ count' = valCount[self]
                       /\ succeedOp' = [succeedOp EXCEPT ![self] = TRUE]
                       /\ txStatus' = [[p \in PROCS |-> IF txStatus[p] = "started"
                                                       THEN "aborted"
                                                       ELSE txStatus[p]]
                                                       EXCEPT ![self] = "none"]
                  ELSE /\ txStatus' = [txStatus EXCEPT ![self] = "aborted"]
                       /\ UNCHANGED << count, succeedOp >>
            /\ IF txStatus'[self] # "aborted"
                  THEN /\ permitNum' = [permitNum EXCEPT ![self] = permitNum[self] + (expVal[self] - newVal[self])]
                  ELSE /\ TRUE
                       /\ UNCHANGED permitNum
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << opIndicator, stack, expVal, newVal, retVal, 
                            valCount, acquires, available_, remaining_, 
                            releases, available, remaining >>

s5(self) == /\ pc[self] = "s5"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ valCount' = [valCount EXCEPT ![self] = Head(stack[self]).valCount]
            /\ expVal' = [expVal EXCEPT ![self] = Head(stack[self]).expVal]
            /\ newVal' = [newVal EXCEPT ![self] = Head(stack[self]).newVal]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

compare_and_set_state(self) == ts(self) \/ s1(self) \/ s2(self) \/ s3(self)
                                  \/ s4(self) \/ tc(self) \/ s5(self)

a1(self) == /\ pc[self] = "a1"
            /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << count, txStatus, opIndicator, permitNum, stack, 
                            expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

a2(self) == /\ pc[self] = "a2"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ available_' = [available_ EXCEPT ![self] = count]
                       /\ pc' = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a5"]
                       /\ UNCHANGED available_
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            remaining_, releases, available, remaining >>

a3(self) == /\ pc[self] = "a3"
            /\ remaining_' = [remaining_ EXCEPT ![self] = available_[self] - acquires[self]]
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, releases, available, remaining >>

a4(self) == /\ pc[self] = "a4"
            /\ IF remaining_[self] >= 0
                  THEN /\ /\ expVal' = [expVal EXCEPT ![self] = available_[self]]
                          /\ newVal' = [newVal EXCEPT ![self] = remaining_[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare_and_set_state",
                                                                   pc        |->  "a2",
                                                                   retVal    |->  retVal[self],
                                                                   valCount  |->  valCount[self],
                                                                   expVal    |->  expVal[self],
                                                                   newVal    |->  newVal[self] ] >>
                                                               \o stack[self]]
                       /\ retVal' = [retVal EXCEPT ![self] = FALSE]
                       /\ valCount' = [valCount EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "ts"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a2"]
                       /\ UNCHANGED << stack, expVal, newVal, retVal, valCount >>
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

a5(self) == /\ pc[self] = "a5"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            expVal, newVal, retVal, valCount, releases, 
                            available, remaining >>

acquire(self) == a1(self) \/ a2(self) \/ a3(self) \/ a4(self) \/ a5(self)

r1(self) == /\ pc[self] = "r1"
            /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << count, txStatus, opIndicator, permitNum, stack, 
                            expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

r2(self) == /\ pc[self] = "r2"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ available' = [available EXCEPT ![self] = count]
                       /\ pc' = [pc EXCEPT ![self] = "r3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r5"]
                       /\ UNCHANGED available
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, remaining >>

r3(self) == /\ pc[self] = "r3"
            /\ remaining' = [remaining EXCEPT ![self] = available[self] + releases[self]]
            /\ pc' = [pc EXCEPT ![self] = "r4"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available >>

r4(self) == /\ pc[self] = "r4"
            /\ /\ expVal' = [expVal EXCEPT ![self] = available[self]]
               /\ newVal' = [newVal EXCEPT ![self] = remaining[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare_and_set_state",
                                                        pc        |->  "r2",
                                                        retVal    |->  retVal[self],
                                                        valCount  |->  valCount[self],
                                                        expVal    |->  expVal[self],
                                                        newVal    |->  newVal[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ valCount' = [valCount EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

r5(self) == /\ pc[self] = "r5"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_ >>

release(self) == r1(self) \/ r2(self) \/ r3(self) \/ r4(self) \/ r5(self)

u1(self) == /\ pc[self] = "u1"
            /\ pc' = [pc EXCEPT ![self] = "u2"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

u2(self) == /\ pc[self] = "u2"
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
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            expVal, newVal, retVal, valCount, releases, 
                            available, remaining >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            stack, expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

u3(self) == /\ pc[self] = "u3"
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
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, permitNum, 
                            expVal, newVal, retVal, valCount, acquires, 
                            available_, remaining_ >>

proc(self) == u1(self) \/ u2(self) \/ cs(self) \/ u3(self)

Next == (\E self \in ProcSet:  \/ compare_and_set_state(self)
                               \/ acquire(self) \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Tue Jun 23 00:46:25 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
