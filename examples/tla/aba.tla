-------------------------------- MODULE aba --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc
CONSTANT N, T, F

ASSUME NbOfCorrProc = N - F
ASSUME N > 3 * T
    /\ T >= F
    /\ T >= 1

VARIABLES ProcessesLocations, nsntEC, nsntRD

--------------------------------------------------------------------------------
TypeOk == nsntEC \in Nat
    /\ ProcessesLocations \in [Processes -> {"loc0", "loc1", "locEC", "locRD", "locAC"}]
    /\ nsntRD \in Nat 

Init == ProcessesLocations \in [Processes -> {"loc0", "loc1"}] 
    /\ nsntEC = 0
    /\ nsntRD = 0

--------------------------------------------------------------------------------
Rule0(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locEC"]
    /\ nsntEC' = nsntEC + 1                   
    /\ UNCHANGED <<nsntRD>>
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc0"
    /\ 2 * nsntEC >= N + T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locEC"]
    /\ nsntEC' = nsntEC + 1                    
    /\ UNCHANGED <<nsntRD>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "loc0"
    /\ nsntRD >= T + 1 - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locEC"]
    /\ nsntEC' = nsntEC + 1
    /\ UNCHANGED <<nsntRD>>
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "locEC"
    /\ 2 * nsntEC >= N + T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locRD"]
    /\ nsntRD' = nsntRD + 1
    /\ UNCHANGED << nsntEC>>
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locEC"
    /\ nsntRD >= T + 1 - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locRD"]
    /\ nsntRD' = nsntRD + 1
    /\ UNCHANGED << nsntEC>>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "locRD"
    /\ 2 * nsntRD >= 2 * T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ UNCHANGED <<nsntEC, nsntRD>>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "loc0"
    /\ 2 * nsntEC < N + T + 1
    /\ nsntRD < T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc0"]
    /\ UNCHANGED <<nsntEC, nsntRD>>
--------------------------------------------------------------------------------                  
Rule7(p) == ProcessesLocations[p] = "locEC"
    /\ 2 * nsntEC < N + T + 1
    /\ nsntRD < T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locEC"]
    /\ UNCHANGED << nsntEC, nsntRD>>
--------------------------------------------------------------------------------
Rule8(p) == ProcessesLocations[p] = "locRD"
    /\ nsntRD < 2 * T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locRD"]
    /\ UNCHANGED <<nsntEC, nsntRD>>
--------------------------------------------------------------------------------
Rule9(p) == ProcessesLocations[p] = "locAC"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ UNCHANGED <<nsntEC, nsntRD>> 
--------------------------------------------------------------------------------

Next == \E p \in Processes: Rule0(p)
        \/ Rule1(p)
        \/ Rule2(p)
        \/ Rule3(p)
        \/ Rule4(p)
        \/ Rule5(p)
        \/ Rule6(p)
        \/ Rule7(p)
        \/ Rule8(p)
        \/ Rule9(p)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_<< ProcessesLocations,nsntEC,nsntRD >>
--------------------------------------------------------------------------------

Nloc0 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})
Nloc1 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc1"})
NlocEC == Cardinality({p \in Processes : ProcessesLocations[p] = "locEC"})
NlocAC == Cardinality({p \in Processes : ProcessesLocations[p] = "locAC"})                    
NlocRD == Cardinality({p \in Processes : ProcessesLocations[p] = "locRD"}) 
                                      
unforg == Nloc1 = 0 => [] (NlocAC = 0)
        
corr == 
    <>[](
        (
            ((2 * nsntEC < N + T + 1) \/ (Nloc0 = 0))
                /\ ((nsntRD < T + 1) \/ (Nloc0 = 0))
                /\ ((2 * nsntEC < N + T + 1) \/ (NlocEC = 0))
                /\ ((nsntRD < T + 1) \/ (NlocEC = 0))
                /\ ((nsntRD < 2 * T + 1) \/ (NlocRD = 0))
                /\ (Nloc1 = 0)
        )
        => ((Nloc0 = 0) => <>(NlocAC /= 0))
    )
  
agreement ==
    <>[](
        (
            ((2 * nsntEC < N + T + 1) \/ (Nloc0 = 0))
            /\ ((nsntRD < T + 1) \/ (Nloc0 = 0))
            /\ ((2 * nsntEC < N + T + 1) \/ (NlocEC = 0))
            /\ ((nsntRD < T + 1) \/ (NlocEC = 0))
            /\ ((nsntRD < 2 * T + 1) \/ (NlocRD = 0))
            /\ (Nloc1 = 0)
        )
        => [](
                (NlocAC /= 0)
                => <>((Nloc0 = 0) /\ (Nloc1 = 0) /\ (NlocEC = 0) /\ (NlocRD = 0))
            )
    )
=============================================================================
