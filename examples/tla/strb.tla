-------------------------------- MODULE strb -----------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N, T, F

ASSUME NbOfCorrProc = N - F
    /\ N > 3 * T
    /\ T >= F
    /\ T >= 1

VARIABLES ProcessesLocations, nsnt
--------------------------------------------------------------------------------

TypeOk == nsnt \in Nat
    /\ ProcessesLocations \in [Processes -> {"loc0", "loc1", "locSE", "locAC"}]

Init == nsnt = 0
    /\ ProcessesLocations \in [Processes -> {"loc0", "loc1"}]
--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"] 
    /\ nsnt' = nsnt + 1
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc0"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ nsnt' = nsnt + 1
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "loc1"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ nsnt' = nsnt + 1 
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "loc0"
    /\ nsnt >= T + 1 - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]                    
    /\ nsnt' = nsnt + 1
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locSE"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ UNCHANGED << nsnt >>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc0"]
    /\ UNCHANGED << nsnt >>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "locSE"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]
    /\ UNCHANGED <<nsnt>>
--------------------------------------------------------------------------------
 Rule7(p) == ProcessesLocations[p] = "locAC"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ UNCHANGED << nsnt >>
--------------------------------------------------------------------------------
Next == \E p \in Processes:
                            \/ Rule0(p)
                            \/ Rule1(p)
                            \/ Rule2(p)
                            \/ Rule3(p)
                            \/ Rule4(p)
                            \/ Rule5(p)
                            \/ Rule6(p)
                            \/ Rule7(p)

Spec == Init /\ [][Next]_<< ProcessesLocations, nsnt >> 
--------------------------------------------------------------------------------

NumInloc0 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})
NumInloc1 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc1"})
NumInlocAC == Cardinality({p \in Processes : ProcessesLocations[p] = "locAC"})
NumInlocSE == Cardinality({p \in Processes : ProcessesLocations[p] = "locSE"})

unforg ==
  (NumInloc1 = 0) => [](NumInlocAC = 0)

corr ==
  <>[](
      (((nsnt < T + 1) \/ (NumInloc0 = 0))
       /\ ((nsnt < N - T) \/ (NumInloc0 = 0))
       /\ ((nsnt < N - T) \/ (NumInlocSE = 0))
       /\ (NumInloc1 = 0))
  )
  =>
  ((NumInloc0 = 0) => <> (NumInlocAC /= 0))

relay ==
  <>[](
      (((nsnt < T + 1) \/ (NumInloc0 = 0))
       /\ ((nsnt < N - T) \/ (NumInloc0 = 0))
       /\ ((nsnt < N - T) \/ (NumInlocSE = 0))
       /\ (NumInloc1 = 0))
  )
  =>
  []((NumInlocAC /= 0) => <> ((NumInloc0 = 0) /\ (NumInloc1 = 0) /\ (NumInlocSE = 0)))

=============================================================================
