------------------------------ MODULE SRB --------------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N, T, F

ASSUME NbOfCorrProc = N - F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

VARIABLES ProcessesLocations, nsnt, rDone

TypeOk == rDone \in Nat 
    /\ nsnt \in Nat
    /\ ProcessesLocations \in [Processes -> {"V0", "V1", "SE", "AC", "fRound"}] 

Init == ProcessesLocations \in [Processes -> {"V0"}]
    /\ nsnt = 0
    /\ rDone = 0
--------------------------------------------------------------------------------
Rule0(p) == ProcessesLocations[p] = "V0"
    /\ nsnt >= T - F + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "SE"]
    /\ nsnt' = nsnt + 1
    /\ UNCHANGED <<rDone>>                         
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "V0"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "AC"]
    /\ UNCHANGED <<nsnt, rDone>>               
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "V1"                  
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "SE"]
    /\ nsnt' = nsnt + 1
    /\ UNCHANGED <<rDone>> 
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "V1"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "AC"]
    /\ UNCHANGED <<nsnt, rDone>>
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "SE"
    /\ nsnt >= N - T - F                    
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "AC"]
    /\ UNCHANGED <<nsnt, rDone>>                   
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "AC"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "fRound"]
    /\ rDone' = rDone + 1 
    /\ UNCHANGED <<nsnt>>        
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "fRound"
    /\ rDone >= N - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "V1"]
    /\ nsnt' = 0
    /\ rDone' = 0
--------------------------------------------------------------------------------
Rule7(p) == ProcessesLocations[p] = "fRound"
    /\ rDone > 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "V1"]
    /\ UNCHANGED <<nsnt, rDone>>                     
--------------------------------------------------------------------------------

Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p) 
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p)
                            
Spec == Init /\ [][Next]_<< ProcessesLocations,nsnt,rDone >>
--------------------------------------------------------------------------------

NumInV1 == Cardinality({p \in Processes : ProcessesLocations[p] = "V1"})
NumInAC == Cardinality({p \in Processes : ProcessesLocations[p] = "AC"}) 

validity1 == 
        NumInV1 = 0 => [] (NumInAC = 0)                    

=============================================================================
