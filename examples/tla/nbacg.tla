------------------------------- MODULE nbacg -----------------------------------

EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N

ASSUME NbOfCorrProc = N
    /\ N > 1

VARIABLES ProcessesLocations, nsntNoCF, nsntYesCF
--------------------------------------------------------------------------------

TypeOk ==  nsntNoCF \in Nat
    /\ nsntYesCF \in Nat
    /\ ProcessesLocations \in [Processes -> {"locNO", "locYES", "locNOFD", "locYESFD", "locSE", "locCMT", "locABR", "locCR"}]

Init == nsntYesCF = 0
    /\ nsntNoCF = 0
    /\ ProcessesLocations \in [Processes -> {"locNO", "locYES", "locNOFD", "locYESFD"}]
--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "locNO"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]
    /\ nsntNoCF' = nsntNoCF + 1                  
    /\ UNCHANGED << nsntYesCF>>
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "locYES"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]
    /\ nsntYesCF' = nsntYesCF + 1
    /\ UNCHANGED << nsntNoCF>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "locNOFD"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locABR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "locYESFD"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locABR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locSE"
    /\ nsntNoCF >= 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locABR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "locSE"
    /\ nsntNoCF < 1
    /\ nsntYesCF >= N
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCMT"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "locNO"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>               
--------------------------------------------------------------------------------
Rule7(p) == ProcessesLocations[p] = "locNOFD"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule8(p) == ProcessesLocations[p] = "locYES"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>  
--------------------------------------------------------------------------------
Rule9(p) == ProcessesLocations[p] = "locYESFD"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED<<nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule10(p) == ProcessesLocations[p] = "locSE"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule11(p) == ProcessesLocations[p] = "locCMT"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule12(p) == ProcessesLocations[p] = "locABR"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule13(p) == ProcessesLocations[p] = "locSE"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule14(p) == ProcessesLocations[p] = "locCMT"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCMT"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------
Rule15(p) == ProcessesLocations[p] = "locABR"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locABR"]
    /\ UNCHANGED << nsntNoCF, nsntYesCF>>
--------------------------------------------------------------------------------

Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p) 
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p) \/ Rule8(p) \/ Rule9(p)
    \/ Rule10(p) \/ Rule11(p) \/ Rule12(p) \/ Rule13(p) \/ Rule14(p) 
    \/ Rule15(p)

Spec == Init /\ [][Next]_<< ProcessesLocations,nsntNoCF,nsntYesCF >>
--------------------------------------------------------------------------------

NumInlocNOFD == Cardinality({ p \in Processes : ProcessesLocations[p] = "locNOFD" })
NumInlocYESFD == Cardinality({ p \in Processes : ProcessesLocations[p] = "locYESFD" })
NumInlocNO == Cardinality({p \in Processes : ProcessesLocations[p] = "locNO"})
NumInlocSE == Cardinality({p \in Processes : ProcessesLocations[p] = "locSE"})
NumInlocYES == Cardinality({p \in Processes : ProcessesLocations[p] = "locYES"})
NumInlocCMT == Cardinality({p \in Processes : ProcessesLocations[p] = "locCMT"})
NumInlocCR == Cardinality({p \in Processes : ProcessesLocations[p] = "locCR"})
NumInlocABR == Cardinality({p \in Processes : ProcessesLocations[p] = "locABR"})

agreement ==
  []((NumInlocCMT = 0) \/ (NumInlocABR = 0))

abort_validity ==
  ((NumInlocNO > 0) \/ (NumInlocNOFD > 0)) => [](NumInlocCMT = 0)

commit_validity ==
  ((NumInlocNO = 0) /\ (NumInlocNOFD = 0) /\ (NumInlocYESFD = 0)) => [](NumInlocABR = 0)

termination ==
  ((<>[]((NumInlocNO = 0) /\ (NumInlocNOFD = 0) /\ (NumInlocYES = 0) /\ (NumInlocYESFD = 0)
           /\ (((nsntNoCF < 1) \/ (NumInlocSE = 0))
               /\ (((nsntYesCF < N) \/ (nsntNoCF >= 1)) \/ (NumInlocSE = 0)))))
   /\ [](NumInlocCR = 0))
  =>
  <>((NumInlocNO = 0) /\ (NumInlocNOFD = 0) /\ (NumInlocYES = 0) /\ (NumInlocYESFD = 0) /\ (NumInlocCR = 0))

=============================================================================
