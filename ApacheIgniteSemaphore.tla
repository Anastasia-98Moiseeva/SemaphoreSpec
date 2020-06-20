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
    succeedOp = [p \in PROCS |-> FALSE];
    txStatus = [p \in PROCS |-> "none"];
    opIndicator = [p \in PROCS |-> "none"];
    
define {

    TypeInv == count \in 0..SEMAFORE_CAPACITY
    
    ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY
    
    PermitInv == IF \A p \in PROCS : /\ txStatus[p] = "none" 
                                     /\ pc[p] \notin {"ts", "ts1", "s5"}
                 THEN Cardinality({p \in PROCS: \/ pc[p] \in {"cs", "u3", "a3", "r2"}
                                                \/ /\ pc[p] = "r1"
                                                   /\ succeedOp[p] = FALSE
                                                \/ /\ pc[p] = "a1"
                                                   /\ succeedOp[p]}) * NUM_OF_PERMITS + count = SEMAFORE_CAPACITY
                 ELSE TRUE
    
    TxInv == \A p \in PROCS : txStatus[p] \in {"none", "started", "committed", "aborted"}

                                            
    ReadyToCommit == \A p \in PROCS : \/ txStatus[p] # "started"
                                      \/ /\ txStatus[p] = "started"
                                         /\ pc[p] \in {"a1", "a2", "r1", "r2"}
    
    CommitAvailable == \A p \in PROCS : \/ txStatus[p] = "none"
                                        \/ txStatus[p] = "started"                                                               
}

procedure start_transaction()
{
ts1:      txStatus[self] := "started";    
          return;  
}

procedure commit_transaction(valCount)
{
tc1:       if (CommitAvailable) {     
               count := valCount;
               succeedOp[self] := TRUE;       
               txStatus[self] := "committed";
           } else {
               txStatus[self] := "aborted"
           };
tc2:       await ReadyToCommit; 
           txStatus[self] := "none";    
           return;
}

procedure compare_and_set_state(expVal, newVal)

variables 
    retVal = FALSE;
    valCount;
{
ts:        call start_transaction();

s1:        valCount := count;       

s2:        if (valCount = expVal) {
               retVal := TRUE
           };
                  
s3:        if (retVal) { 

s4:            valCount := newVal;

tc:            call commit_transaction(valCount);
           };
s5:        return; 

}

procedure acquire(acquires)

variables 
    available;
    remaining;  
{    
a1:        while (succeedOp[self] = FALSE) {

               available := count;
               remaining := available - acquires;  
                    
a2:            await remaining >= 0;  
               call compare_and_set_state(available, remaining)       
           };
       
a3:        succeedOp[self] := FALSE;
           return;      
}

procedure release(releases)

variables 
    available;
    remaining;
{     
r1:        while (succeedOp[self] = FALSE) { 

               available := count;
               remaining := available + releases;
           
r2:            call compare_and_set_state(available, remaining)
           };
       
r3:        succeedOp[self] := FALSE;
           return;
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
\* Procedure variable valCount of procedure compare_and_set_state at line 71 col 5 changed to valCount_
\* Procedure variable available of procedure acquire at line 94 col 5 changed to available_
\* Procedure variable remaining of procedure acquire at line 95 col 5 changed to remaining_
CONSTANT defaultInitValue
VARIABLES count, succeedOp, txStatus, opIndicator, pc, stack

(* define statement *)
TypeInv == count \in 0..SEMAFORE_CAPACITY

ExcInv == Cardinality({p \in PROCS: pc[p] = "cs"}) * NUM_OF_PERMITS <= SEMAFORE_CAPACITY

PermitInv == IF \A p \in PROCS : /\ txStatus[p] = "none"
                                 /\ pc[p] \notin {"ts", "ts1", "s5"}
             THEN Cardinality({p \in PROCS: \/ pc[p] \in {"cs", "u3", "a3", "r2"}
                                            \/ /\ pc[p] = "r1"
                                               /\ succeedOp[p] = FALSE
                                            \/ /\ pc[p] = "a1"
                                               /\ succeedOp[p]}) * NUM_OF_PERMITS + count = SEMAFORE_CAPACITY
             ELSE TRUE

TxInv == \A p \in PROCS : txStatus[p] \in {"none", "started", "committed", "aborted"}


ReadyToCommit == \A p \in PROCS : \/ txStatus[p] # "started"
                                  \/ /\ txStatus[p] = "started"
                                     /\ pc[p] \in {"a1", "a2", "r1", "r2"}

CommitAvailable == \A p \in PROCS : \/ txStatus[p] = "none"
                                    \/ txStatus[p] = "started"

VARIABLES valCount, expVal, newVal, retVal, valCount_, acquires, available_, 
          remaining_, releases, available, remaining

vars == << count, succeedOp, txStatus, opIndicator, pc, stack, valCount, 
           expVal, newVal, retVal, valCount_, acquires, available_, 
           remaining_, releases, available, remaining >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ count = SEMAFORE_CAPACITY
        /\ succeedOp = [p \in PROCS |-> FALSE]
        /\ txStatus = [p \in PROCS |-> "none"]
        /\ opIndicator = [p \in PROCS |-> "none"]
        (* Procedure commit_transaction *)
        /\ valCount = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure compare_and_set_state *)
        /\ expVal = [ self \in ProcSet |-> defaultInitValue]
        /\ newVal = [ self \in ProcSet |-> defaultInitValue]
        /\ retVal = [ self \in ProcSet |-> FALSE]
        /\ valCount_ = [ self \in ProcSet |-> defaultInitValue]
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

ts1(self) == /\ pc[self] = "ts1"
             /\ txStatus' = [txStatus EXCEPT ![self] = "started"]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << count, succeedOp, opIndicator, valCount, expVal, 
                             newVal, retVal, valCount_, acquires, available_, 
                             remaining_, releases, available, remaining >>

start_transaction(self) == ts1(self)

tc1(self) == /\ pc[self] = "tc1"
             /\ IF CommitAvailable
                   THEN /\ count' = valCount[self]
                        /\ succeedOp' = [succeedOp EXCEPT ![self] = TRUE]
                        /\ txStatus' = [txStatus EXCEPT ![self] = "committed"]
                   ELSE /\ txStatus' = [txStatus EXCEPT ![self] = "aborted"]
                        /\ UNCHANGED << count, succeedOp >>
             /\ pc' = [pc EXCEPT ![self] = "tc2"]
             /\ UNCHANGED << opIndicator, stack, valCount, expVal, newVal, 
                             retVal, valCount_, acquires, available_, 
                             remaining_, releases, available, remaining >>

tc2(self) == /\ pc[self] = "tc2"
             /\ ReadyToCommit
             /\ txStatus' = [txStatus EXCEPT ![self] = "none"]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ valCount' = [valCount EXCEPT ![self] = Head(stack[self]).valCount]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << count, succeedOp, opIndicator, expVal, newVal, 
                             retVal, valCount_, acquires, available_, 
                             remaining_, releases, available, remaining >>

commit_transaction(self) == tc1(self) \/ tc2(self)

ts(self) == /\ pc[self] = "ts"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "start_transaction",
                                                     pc        |->  "s1" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "ts1"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, valCount, 
                            expVal, newVal, retVal, valCount_, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s1(self) == /\ pc[self] = "s1"
            /\ valCount_' = [valCount_ EXCEPT ![self] = count]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, retVal, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s2(self) == /\ pc[self] = "s2"
            /\ IF valCount_[self] = expVal[self]
                  THEN /\ retVal' = [retVal EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED retVal
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, valCount_, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

s3(self) == /\ pc[self] = "s3"
            /\ IF retVal[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "s4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, retVal, valCount_, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

s4(self) == /\ pc[self] = "s4"
            /\ valCount_' = [valCount_ EXCEPT ![self] = newVal[self]]
            /\ pc' = [pc EXCEPT ![self] = "tc"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, retVal, acquires, 
                            available_, remaining_, releases, available, 
                            remaining >>

tc(self) == /\ pc[self] = "tc"
            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "commit_transaction",
                                                        pc        |->  "s5",
                                                        valCount  |->  valCount[self] ] >>
                                                    \o stack[self]]
               /\ valCount' = [valCount EXCEPT ![self] = valCount_[self]]
            /\ pc' = [pc EXCEPT ![self] = "tc1"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, expVal, 
                            newVal, retVal, valCount_, acquires, available_, 
                            remaining_, releases, available, remaining >>

s5(self) == /\ pc[self] = "s5"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ retVal' = [retVal EXCEPT ![self] = Head(stack[self]).retVal]
            /\ valCount_' = [valCount_ EXCEPT ![self] = Head(stack[self]).valCount_]
            /\ expVal' = [expVal EXCEPT ![self] = Head(stack[self]).expVal]
            /\ newVal' = [newVal EXCEPT ![self] = Head(stack[self]).newVal]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, valCount, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

compare_and_set_state(self) == ts(self) \/ s1(self) \/ s2(self) \/ s3(self)
                                  \/ s4(self) \/ tc(self) \/ s5(self)

a1(self) == /\ pc[self] = "a1"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ available_' = [available_ EXCEPT ![self] = count]
                       /\ remaining_' = [remaining_ EXCEPT ![self] = available_'[self] - acquires[self]]
                       /\ pc' = [pc EXCEPT ![self] = "a2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a3"]
                       /\ UNCHANGED << available_, remaining_ >>
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, retVal, valCount_, 
                            acquires, releases, available, remaining >>

a2(self) == /\ pc[self] = "a2"
            /\ remaining_[self] >= 0
            /\ /\ expVal' = [expVal EXCEPT ![self] = available_[self]]
               /\ newVal' = [newVal EXCEPT ![self] = remaining_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare_and_set_state",
                                                        pc        |->  "a1",
                                                        retVal    |->  retVal[self],
                                                        valCount_ |->  valCount_[self],
                                                        expVal    |->  expVal[self],
                                                        newVal    |->  newVal[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ valCount_' = [valCount_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, valCount, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

a3(self) == /\ pc[self] = "a3"
            /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available_' = [available_ EXCEPT ![self] = Head(stack[self]).available_]
            /\ remaining_' = [remaining_ EXCEPT ![self] = Head(stack[self]).remaining_]
            /\ acquires' = [acquires EXCEPT ![self] = Head(stack[self]).acquires]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, txStatus, opIndicator, valCount, expVal, 
                            newVal, retVal, valCount_, releases, available, 
                            remaining >>

acquire(self) == a1(self) \/ a2(self) \/ a3(self)

r1(self) == /\ pc[self] = "r1"
            /\ IF succeedOp[self] = FALSE
                  THEN /\ available' = [available EXCEPT ![self] = count]
                       /\ remaining' = [remaining EXCEPT ![self] = available'[self] + releases[self]]
                       /\ pc' = [pc EXCEPT ![self] = "r2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "r3"]
                       /\ UNCHANGED << available, remaining >>
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, retVal, valCount_, 
                            acquires, available_, remaining_, releases >>

r2(self) == /\ pc[self] = "r2"
            /\ /\ expVal' = [expVal EXCEPT ![self] = available[self]]
               /\ newVal' = [newVal EXCEPT ![self] = remaining[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare_and_set_state",
                                                        pc        |->  "r1",
                                                        retVal    |->  retVal[self],
                                                        valCount_ |->  valCount_[self],
                                                        expVal    |->  expVal[self],
                                                        newVal    |->  newVal[self] ] >>
                                                    \o stack[self]]
            /\ retVal' = [retVal EXCEPT ![self] = FALSE]
            /\ valCount_' = [valCount_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ts"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, valCount, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

r3(self) == /\ pc[self] = "r3"
            /\ succeedOp' = [succeedOp EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ available' = [available EXCEPT ![self] = Head(stack[self]).available]
            /\ remaining' = [remaining EXCEPT ![self] = Head(stack[self]).remaining]
            /\ releases' = [releases EXCEPT ![self] = Head(stack[self]).releases]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << count, txStatus, opIndicator, valCount, expVal, 
                            newVal, retVal, valCount_, acquires, available_, 
                            remaining_ >>

release(self) == r1(self) \/ r2(self) \/ r3(self)

u1(self) == /\ pc[self] = "u1"
            /\ pc' = [pc EXCEPT ![self] = "u2"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, retVal, valCount_, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

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
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, valCount, 
                            expVal, newVal, retVal, valCount_, releases, 
                            available, remaining >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, stack, 
                            valCount, expVal, newVal, retVal, valCount_, 
                            acquires, available_, remaining_, releases, 
                            available, remaining >>

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
            /\ UNCHANGED << count, succeedOp, txStatus, opIndicator, valCount, 
                            expVal, newVal, retVal, valCount_, acquires, 
                            available_, remaining_ >>

proc(self) == u1(self) \/ u2(self) \/ cs(self) \/ u3(self)

Next == (\E self \in ProcSet:  \/ start_transaction(self)
                               \/ commit_transaction(self)
                               \/ compare_and_set_state(self)
                               \/ acquire(self) \/ release(self))
           \/ (\E self \in PROCS: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Sat Jun 20 23:09:59 MSK 2020 by anastasia
\* Created Tue Mar 24 22:27:24 MSK 2020 by anastasia
