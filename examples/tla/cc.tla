--------------------------------- MODULE cc ------------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N, F, T

ASSUME NbOfCorrProc = N /\ N > 2 * T /\ T >= F /\ T >= 0 /\ F >= 0

VARIABLES ProcessesLocations, nsnt00, nsnt01,  
    nsnt10, nsnt11, nsnt00plus01, nfaulty


TypeOk == nfaulty \in Nat
    /\ nsnt00 \in Nat
    /\ nsnt01 \in Nat 
    /\ nsnt10 \in Nat
    /\ nsnt11 \in Nat
    /\ nsnt00plus01 \in Nat
    /\ ProcessesLocations \in 
        [Processes -> {"loc0", "loc1", "locP0", "locP1", "locAC0", "locAC1", "locCR" }]


Init == ProcessesLocations \in [Processes -> {"loc0", "loc1" }]
    /\ nsnt00 = 0
    /\ nsnt01 = 0
    /\ nsnt10 = 0 
    /\ nsnt11 = 0 
    /\ nsnt00plus01 = 0
    /\ nfaulty = 0
--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locP0"]
    /\ nsnt00' = nsnt00 + 1
    /\ nsnt00plus01' = nsnt00plus01 + 1                  
    /\ UNCHANGED << nsnt01, nsnt10, nsnt11, nfaulty>>
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locP0"]
    /\ nsnt01' = nsnt01 + 1
    /\ nsnt00plus01' = nsnt00plus01 + 1
    /\ UNCHANGED << nsnt00, nsnt10, nsnt11, nfaulty>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "locP0"
    /\ nsnt00plus01 >= N - T
    /\ 2 * nsnt00 >= N - T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locP1"]
    /\ nsnt10' = nsnt10 + 1
    /\ UNCHANGED << nsnt00, nsnt01, nsnt11, nsnt00plus01, nfaulty>>          
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "locP0"
    /\ nsnt00plus01 >= N - T
    /\ 2 * nsnt01 >= N - T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locP1"]
    /\ nsnt11' = nsnt11 + 1
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt00plus01, nfaulty>>
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locP1"
    /\ 2 * nsnt10 >= N + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC0"]
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01, nfaulty >>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "locP1"
    /\ 2 * nsnt11 >= N + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC1"]
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01, nfaulty >>                
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "locP0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01 >>
--------------------------------------------------------------------------------
Rule7(p) == ProcessesLocations[p] = "locP1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED <<nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01 >>
--------------------------------------------------------------------------------
Rule8(p) == ProcessesLocations[p] = "locAC0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]  
    /\ nfaulty' = nfaulty + 1                
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01 >>
--------------------------------------------------------------------------------
Rule9(p) == ProcessesLocations[p] = "locAC1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01 >>
--------------------------------------------------------------------------------
Rule10(p) == ProcessesLocations[p] = "locP0" 
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locP0"]
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01, nfaulty>>
--------------------------------------------------------------------------------
Rule11(p) == ProcessesLocations[p] = "locP1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locP1"]
    /\ UNCHANGED <<nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01, nfaulty >> 
--------------------------------------------------------------------------------
Rule12(p) == ProcessesLocations[p] = "locAC0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC0"]
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01, nfaulty >>
--------------------------------------------------------------------------------
Rule13(p) == ProcessesLocations[p] = "locAC1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC1"]
    /\ UNCHANGED << nsnt00, nsnt01, nsnt10, nsnt11, nsnt00plus01, nfaulty >>
--------------------------------------------------------------------------------
Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p) 
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p) \/ Rule8(p) \/ Rule9(p)
    \/ Rule10(p) \/ Rule11(p) \/ Rule12(p) \/ Rule13(p)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_<< ProcessesLocations, nsnt00, nsnt01, nsnt10, nsnt11,
                            nsnt00plus01, nfaulty >>
--------------------------------------------------------------------------------

NumInloc1 == Cardinality({ p \in Processes : ProcessesLocations[p] = "loc1" })
NumInloc0 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})
NumInlocAC0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locAC0"})
NumInlocAC1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locAC1"})
NumInlocP0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locP0"})
NumInlocP1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locP1"})


validity0 ==
  (NumInloc0 = 0) => [] (NumInlocAC0 = 0)

validity1 ==
  (NumInloc1 = 0) => [] (NumInlocAC1 = 0)

agreement ==
  [] ((NumInlocAC0 = 0) \/ (NumInlocAC1 = 0))

termination ==
  (((NumInloc0 > NumInloc1 + T) \/ (NumInloc1 > NumInloc0 + T))
    /\ <>[] ( (NumInloc0 = 0) /\ (NumInloc1 = 0)
              /\ ((nsnt00plus01 < N - T) \/ (NumInlocP0 = 0))
              /\ ((2 * nsnt10 < N + 1) \/ (NumInlocP1 = 0))
              /\ ((2 * nsnt11 < N + 1) \/ (NumInlocP1 = 0)) ))
  => <> ((NumInloc0 = 0) /\ (NumInloc1 = 0) /\ (NumInlocP0 = 0) /\ (NumInlocP1 = 0))

================================================================================
