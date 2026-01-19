-------------------------------- MODULE c1cs -----------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N, F, T

ASSUME NbOfCorrProc = N
    /\ N > 3 * T
    /\ T >= F
    /\ T >= 1

VARIABLES ProcessesLocations, nsnt0, nsnt1, nsnt0CF, nsnt1CF, nsnt01, 
    nsnt01CF, nfaulty

--------------------------------------------------------------------------------
TypeOk == nfaulty \in Nat 
    /\ nsnt0 \in Nat
    /\ nsnt1 \in Nat 
    /\ nsnt0CF \in Nat 
    /\ nsnt1CF \in Nat 
    /\ nsnt01 \in Nat
    /\ nsnt01CF \in Nat 
    /\ ProcessesLocations \in 
        [Processes -> {"loc0", "loc1", "locS0", "locS1", "locD0", "locD1", "locU0", "locU1", "locCR" }] 

Init == ProcessesLocations \in [Processes -> {"loc0", "loc1" }]
    /\ nsnt0 = 0 /\ nsnt1 = 0 /\ nsnt0CF = 0 /\ nsnt1CF  = 0 /\ nsnt01 = 0
    /\ nsnt01CF = 0 /\ nfaulty = 0
--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS0"]
    /\ nsnt0CF' = nsnt0CF + 1
    /\ nsnt0' = nsnt0 + 1
    /\ nsnt01CF' = nsnt01CF + 1
    /\ nsnt01' = nsnt01 + 1
    /\ UNCHANGED <<nsnt1, nsnt1CF, nfaulty>>       
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nsnt0CF' = nsnt0CF + 1
    /\ nsnt01CF' = nsnt01CF + 1
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0, nsnt1, nsnt1CF, nsnt01>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS1"]
    /\ nsnt1CF' = nsnt1CF + 1
    /\ nsnt01CF' = nsnt01CF + 1
    /\ nsnt1' = nsnt1 + 1
    /\ nsnt01' = nsnt01 + 1
    /\ UNCHANGED << nsnt0, nsnt0CF, nfaulty>>
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "loc1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED << nsnt0, nsnt0CF, nsnt1, nsnt01>>
    /\ nsnt1CF' = nsnt1CF + 1 /\ nsnt01CF' = nsnt01CF + 1 
    /\ nfaulty' = nfaulty + 1  
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt0CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt0CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt1CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule10(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt1CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule12(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01CF >= N - T
    /\ nsnt0CF >= N - 2 * T
    /\ nsnt1CF >= 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule13(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01CF >= N - T
    /\ nsnt0CF >= N - 2 * T
    /\ nsnt1CF >= 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule14(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01CF >= N - T
    /\ nsnt1CF >= N - 2 * T
    /\ nsnt0CF >= 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule15(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01CF >= N - T
    /\ nsnt1CF >= N - 2 * T
    /\ nsnt0CF >= 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule16(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01CF >= N - T
    /\ nsnt0 < N - 2 * T
    /\ nsnt1 < N - 2 * T    
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule17(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01CF >= N - T
    /\ nsnt0 < N - 2 * T
    /\ nsnt1 < N - 2 * T 
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule18(p) == ProcessesLocations[p] = "loc0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule19(p) == ProcessesLocations[p] = "loc1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule20(p) == ProcessesLocations[p] = "locS0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>> 
--------------------------------------------------------------------------------
Rule21(p) == ProcessesLocations[p] = "locS1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule22(p) == ProcessesLocations[p] = "locD0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule23(p) == ProcessesLocations[p] = "locD1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule24(p) == ProcessesLocations[p] = "locU0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED <<nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule25(p) == ProcessesLocations[p] = "locU1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule26(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc0"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule27(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc1"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule28(p) == ProcessesLocations[p] = "locS0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS0"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule29(p) == ProcessesLocations[p] = "locS1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS1"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule30(p) == ProcessesLocations[p] = "locD0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule31(p) == ProcessesLocations[p] = "locD1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule32(p) == ProcessesLocations[p] = "locU0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule33(p) == ProcessesLocations[p] = "locU1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED <<nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p) 
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule10(p) \/ Rule12(p) \/ Rule13(p)
    \/ Rule14(p) \/ Rule15(p) \/ Rule16(p) \/ Rule17(p) \/ Rule18(p)
    \/ Rule19(p) \/ Rule20(p) \/ Rule21(p) \/ Rule22(p) \/ Rule23(p) 
    \/ Rule24(p) \/ Rule25(p) \/ Rule26(p) \/ Rule27(p) \/ Rule28(p) 
    \/ Rule29(p) \/ Rule30(p) \/ Rule31(p) \/ Rule32(p) \/ Rule33(p)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_<< ProcessesLocations, nsnt0, nsnt1, nsnt0CF, nsnt1CF, 
                            nsnt01, nsnt01CF, nfaulty >>
--------------------------------------------------------------------------------

NumInloc0 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})
NumInloc1 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc1"})
NumInlocD1 == Cardinality({ p \in Processes : ProcessesLocations[p] = "locD1" })
NumInlocD0 == Cardinality({ p \in Processes : ProcessesLocations[p] = "locD0" })
NumInlocS1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locS1"})
NumInlocU0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locU0"})
NumInlocU1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locU1"})
NumInlocS0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locS0"})


one_step0 ==
  (NumInloc1 = 0 => [] (NumInlocD1 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))

one_step1 ==
  (NumInloc0 = 0 => [] (NumInlocD0 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))


fast0 ==
  (<>[]((nsnt01CF < N - T \/ (NumInlocS0 = 0 /\ NumInlocS1 = 0))
       /\ NumInloc0 = 0 /\ NumInloc1 = 0))
  =>
  (NumInloc1 = 0 => <> (NumInloc0 = 0 /\ NumInloc1 = 0 /\ NumInlocS0 = 0 /\ NumInlocS1 = 0
                      /\ NumInlocD1 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))

fast1 ==
  (<>[]((nsnt01CF < N - T \/ (NumInlocS0 = 0 /\ NumInlocS1 = 0))
       /\ NumInloc0 = 0 /\ NumInloc1 = 0))
  =>
  (NumInloc0 = 0 => <> (NumInloc0 = 0 /\ NumInloc1 = 0 /\ NumInlocS0 = 0 /\ NumInlocS1 = 0
                      /\ NumInlocD0 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))

termination ==
  (<>[] ((nsnt01CF < N - T \/ (NumInlocS0 = 0 /\ NumInlocS1 = 0))
       /\ NumInloc0 = 0 /\ NumInloc1 = 0))
  =>
  <> (NumInloc0 = 0 /\ NumInloc1 = 0 /\ NumInlocS0 = 0 /\ NumInlocS1 = 0)

=============================================================================
