-------------------------------- MODULE frb ------------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N, T, F

ASSUME NbOfCorrProc = N 
    /\ N >= 1
    /\ N > T
    /\ T >= F


VARIABLES ProcessesLocations, nsnt, nsntF,  nfaulty
--------------------------------------------------------------------------------

TypeOk == ProcessesLocations \in [Processes -> {"loc0", "loc1", "locCR", "locAC"}]
    /\ nsnt \in Nat
    /\ nsntF \in Nat 
    /\ nfaulty \in Nat

Init ==  ProcessesLocations \in [Processes -> {"loc0", "loc1"}]
    /\ nsnt = 0
    /\ nsntF = 0
    /\ nfaulty = 0
--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "loc0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"] 
    /\ nfaulty' = nfaulty + 1                 
    /\ UNCHANGED <<nsnt, nsntF>>
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1                    
    /\ UNCHANGED <<nsnt, nsntF>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "loc1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nsntF' = nsntF + 1
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED <<nsnt>>
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "locAC"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]                    
    /\ nfaulty' = nfaulty + 1 
    /\ UNCHANGED << nsnt, nsntF>>
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "loc1"
    /\ nsnt >= 0
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ nsnt' = nsnt + 1
    /\ UNCHANGED << nsntF, nfaulty >>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "loc0"
    /\ nsnt >= 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ nsnt' = nsnt + 1
    /\ UNCHANGED << nsntF, nfaulty >>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "loc0"
    /\ nsnt >= 0
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc0"]
    /\ UNCHANGED <<nsnt, nsntF, nfaulty>>
--------------------------------------------------------------------------------            
 Rule7(p) == ProcessesLocations[p] = "loc1"
    /\ nsnt >= 0
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc1"]
    /\ UNCHANGED << nsnt, nsntF, nfaulty >>
--------------------------------------------------------------------------------
Rule8(p) == ProcessesLocations[p] = "locAC"
    /\ nsnt >= 0
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ UNCHANGED <<nsnt, nsntF, nfaulty >>
--------------------------------------------------------------------------------

Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p) 
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p) \/ Rule8(p)

Spec == Init /\ [][Next]_<< ProcessesLocations,nsnt,nsntF,nfaulty >>
--------------------------------------------------------------------------------

NumInloc1 == Cardinality({p \in Processes: ProcessesLocations[p] = "loc1"})
NumInlocAC == Cardinality({p \in Processes: ProcessesLocations[p] = "locAC"})

\* safety 
unforg == 
        NumInloc1 = 0 => [](NumInlocAC = 0)

\* the following two liveness properties require fairness constraints
NumInloc0 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})

corr ==
    <>[]((nsnt < 1 \/ NumInloc0 = 0) /\ (nsnt < 0 \/ NumInloc1 = 0))
    =>
    (NumInloc0 = 0 => <> (NumInlocAC /= 0))

relay == 
    <>[]((nsnt < 1 \/ NumInloc0 = 0) /\ (nsnt < 0 \/ NumInloc1 = 0))
    =>
    []((NumInlocAC /= 0) => <> ((NumInloc0 = 0) /\ (NumInloc1 = 0)))

================================================================================
