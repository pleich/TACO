-------------------------------- MODULE cf1s -----------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N, F, T

ASSUME NbOfCorrProc = N
    /\ N > 3 * T
    /\ T >= F
    /\ T >= 1

VARIABLES ProcessesLocations, nsnt0, nsnt1, nsnt01, nsnt0CF, nsnt1CF, nsnt01CF,
    nfaulty
--------------------------------------------------------------------------------

TypeOk == ProcessesLocations \in [Processes -> {"loc0", "loc1", "locS0", "locS1", "locD0", "locD1", "locU0", "locU1", "locCR" }] 
    /\ nsnt0 \in Nat /\ nsnt1 \in Nat /\ nsnt01 \in Nat /\ nsnt0CF \in Nat
    /\ nsnt1CF \in Nat /\ nsnt01CF \in Nat /\ nfaulty \in Nat

Init ==  ProcessesLocations \in [Processes -> {"loc0", "loc1"}] 
    /\ nsnt0 = 0 /\ nsnt1 = 0 /\ nsnt01 = 0 /\ nsnt0CF = 0 /\ nsnt1CF = 0
    /\ nsnt01CF = 0 /\ nfaulty = 0

--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS0"]
    /\ nsnt0CF' = nsnt0CF + 1 
    /\ nsnt0' = nsnt0 + 1 
    /\ nsnt01CF' = nsnt01CF + 1 
    /\ nsnt01' = nsnt01 + 1
    /\ UNCHANGED << nsnt1CF, nsnt1, nfaulty>>         
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nsnt0CF' = nsnt0CF + 1 
    /\ nsnt01CF' = nsnt01CF + 1
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt1CF, nsnt0, nsnt1, nsnt01>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS1"]
    /\ nsnt1CF' = nsnt1CF + 1
    /\ nsnt01CF' = nsnt01CF + 1
    /\ nsnt01' = nsnt01 + 1
    /\ nsnt1' = nsnt1 + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nfaulty>>              
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "loc1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nsnt1CF' = nsnt1CF + 1
    /\ nsnt1' = nsnt1 + 1
    /\ nsnt01CF' = nsnt01CF + 1
    /\ nsnt01' = nsnt01 + 1
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0 >>     
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01CF >= N - T /\ nsnt0CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01CF >= N - T /\ nsnt0CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01CF >= N - T /\ nsnt1CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule7(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01CF >= N - T /\ nsnt1CF >= N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule8(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01CF >= N - T /\ nsnt0 < N - T /\ nsnt1 < N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------
Rule9(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01CF >= N - T /\ nsnt0 < N - T /\ nsnt1 < N - T
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01, nfaulty>>
--------------------------------------------------------------------------------                
Rule10(p) == ProcessesLocations[p] = "loc0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule11(p) == ProcessesLocations[p] = "loc1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule12(p) == ProcessesLocations[p] = "locS0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01 >>
--------------------------------------------------------------------------------
Rule13(p) == ProcessesLocations[p] = "locS1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01 >>  
--------------------------------------------------------------------------------
Rule14(p) == ProcessesLocations[p] = "locD0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01 >>
--------------------------------------------------------------------------------
Rule15(p) == ProcessesLocations[p] = "locD1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01 >>
--------------------------------------------------------------------------------
Rule16(p) == ProcessesLocations[p] = "locU0"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01 >>
--------------------------------------------------------------------------------
Rule17(p) ==  ProcessesLocations[p] = "locU1"
    /\ nfaulty < F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nfaulty' = nfaulty + 1
    /\ UNCHANGED << nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01 >>
--------------------------------------------------------------------------------
Rule18(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc0"]
    /\ UNCHANGED << nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule19(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc1"]
    /\ UNCHANGED << nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule20(p) == ProcessesLocations[p] = "locS0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS0"]
    /\ UNCHANGED << nfaulty,nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule21(p) == ProcessesLocations[p] = "locS1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS1"]
    /\ UNCHANGED << nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule22(p) == ProcessesLocations[p] = "locD0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED << nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule23(p) == ProcessesLocations[p] = "locD1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
    /\ UNCHANGED << nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule24(p) == ProcessesLocations[p] = "locU0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED << nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------
Rule25(p) == ProcessesLocations[p] = "locU1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED << nfaulty, nsnt0CF, nsnt0, nsnt1CF, nsnt1, nsnt01CF, nsnt01>>
--------------------------------------------------------------------------------

Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p)
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p) \/ Rule8(p) \/ Rule9(p)
    \/ Rule10(p) \/ Rule11(p) \/ Rule12(p) \/ Rule13(p) \/ Rule14(p)
    \/ Rule15(p) \/ Rule16(p) \/ Rule17(p) \/ Rule18(p) \/ Rule19(p)
    \/ Rule20(p) \/ Rule21(p) \/ Rule22(p) \/ Rule23(p) \/ Rule24(p)
    \/ Rule25(p)

Spec == Init /\ [][Next]_<< ProcessesLocations, nsnt0, nsnt1, nsnt01, nsnt0CF, 
                            nsnt1CF, nsnt01CF, nfaulty >>
--------------------------------------------------------------------------------

NumInloc1 == Cardinality({ p \in Processes : ProcessesLocations[p] = "loc1" })
NumInlocD1 == Cardinality({ p \in Processes : ProcessesLocations[p] = "locD1" })
NumInlocD0 == Cardinality({ p \in Processes : ProcessesLocations[p] = "locD0" })
NumInloc0 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})
NumInlocS1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locS1"})
NumInlocU0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locU0"})
NumInlocU1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locU1"})
NumInlocS0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locS0"})
NumInlocCR == Cardinality({p \in Processes : ProcessesLocations[p] = "locCR"})

one_step0 ==
  ((NumInloc1 = 0) /\ (F = 0)) => [] ((NumInlocD1 = 0) /\ (NumInlocU0 = 0) /\ (NumInlocU1 = 0))

one_step1 ==
  (NumInloc0 = 0 /\ F = 0 => [] (NumInlocD0 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))

fast0 ==
  (<>[] (((nsnt01 < N - T) \/ ((NumInlocS0 = 0) /\ (NumInlocS1 = 0)))
         /\ (NumInloc0 = 0) /\ (NumInloc1 = 0)))
  =>
  (((NumInloc1 = 0) /\ (F = 0)) => <> ((NumInloc0 = 0) /\ (NumInloc1 = 0) /\ (NumInlocS0 = 0) 
                                        /\ (NumInlocS1 = 0)
                                   /\ (NumInlocD1 = 0) /\ (NumInlocU0 = 0) /\ (NumInlocU1 = 0)))

fast1 ==
  (<>[] ((nsnt01 < N - T \/ (NumInlocS0 = 0 /\ NumInlocS1 = 0))
         /\ NumInloc0 = 0 /\ NumInloc1 = 0))
  =>
  (NumInloc0 = 0 /\ F = 0 => <> (NumInloc0 = 0 /\ NumInloc1 = 0 /\ NumInlocS0 = 0 
                                    /\ NumInlocS1 = 0
                                   /\ NumInlocD0 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))

termination ==
  (<>[] (((nsnt01 < N - T) \/ ((NumInlocS0 = 0) /\ (NumInlocS1 = 0)))
         /\ (NumInloc0 = 0) /\ (NumInloc1 = 0)))
  =>
  <> ((NumInloc0 = 0) /\ (NumInloc1 = 0) /\ (NumInlocS0 = 0) /\ (NumInlocS1 = 0))

=============================================================================
