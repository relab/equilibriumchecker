-------------------------- MODULE FRCheckerCosmos --------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT Corr, Faulty, N, T, ValidValues, InvalidValues, MaxRound, Proposer, Weight  

VARIABLES
  round1,    \* a process round number: Corr -> Rounds
  step1,     \* a process step: Corr -> { "PROPOSE", "PREVOTE", "PRECOMMIT", "DECIDED" }
  decision1, \* process decision: Corr -> ValuesOrNil
  lockedValue1,  \* a locked value: Corr -> ValuesOrNil
  lockedRound1,  \* a locked round: Corr -> RoundsOrNil
  validValue1,   \* a valid value: Corr -> ValuesOrNil
  validRound1,    \* a valid round: Corr -> RoundsOrNil
  msgsPropose1,   \* PROPOSE messages broadcast in the system, Rounds -> Messages
  msgsPrevote1,   \* PREVOTE messages broadcast in the system, Rounds -> Messages
  msgsPrecommit1, \* PRECOMMIT messages broadcast in the system, Rounds -> Messages
  evidence1, \* the messages that were used by the correct processes to make transitions
  action1,        \* we use this variable to see which action was taken
  profit1,         \* we use this variable to indicate the profit of each pricess
  participated1, \* we use this variable to indicate whether ot not a process has voted
  rewarded1,
  numParticipated1,
  rewarddecided1
  
VARIABLES
  round2,    \* a process round number: Corr -> Rounds
  step2,     \* a process step: Corr -> { "PROPOSE", "PREVOTE", "PRECOMMIT", "DECIDED" }
  decision2, \* process decision: Corr -> ValuesOrNil
  lockedValue2,  \* a locked value: Corr -> ValuesOrNil
  lockedRound2,  \* a locked round: Corr -> RoundsOrNil
  validValue2,   \* a valid value: Corr -> ValuesOrNil
  validRound2,    \* a valid round: Corr -> RoundsOrNil
  msgsPropose2,   \* PROPOSE messages broadcast in the system, Rounds -> Messages
  msgsPrevote2,   \* PREVOTE messages broadcast in the system, Rounds -> Messages
  msgsPrecommit2, \* PRECOMMIT messages broadcast in the system, Rounds -> Messages
  evidence2, \* the messages that were used by the correct processes to make transitions
  action2,        \* we use this variable to see which action was taken
  profit2,         \* we use this variable to indicate the profit of each pricess
  participated2, \* we use this variable to indicate whether ot not a process has voted
  rewarded2,
  numParticipated2,
  rewarddecided2
  
VARIABLES rational


vars2 == <<round2, step2, decision2, lockedValue2, lockedRound2, validValue2, validRound2, 
msgsPropose2, msgsPrevote2, msgsPrecommit2, evidence2, action2, profit2, participated2, rewarded2, numParticipated2 >>

AllProcs == Corr \union Faulty

Rounds == 0..MaxRound               \* the set of potential rounds


G1 == INSTANCE Cosmos WITH round <- round1, step <- step1, decision <- decision1, 
                                            lockedValue <- lockedValue1, lockedRound <- lockedRound1, 
                                            validValue <- validValue1, validRound <- validRound1,
                                            msgsPropose <- msgsPropose1, msgsPrevote <- msgsPrevote1,
                                            msgsPrecommit <- msgsPrecommit1, evidence <- evidence1, 
                                            action <- action1, profit <- profit1, rewarded <- rewarded1,  
                                            participated <- participated1, numParticipated <- numParticipated1, 
                                            rewarddecided <- rewarddecided1

G2 == INSTANCE Cosmos WITH round <- round2, step <- step2, decision <- decision2, 
                                            lockedValue <- lockedValue2, lockedRound <- lockedRound2, 
                                            validValue <- validValue2, validRound <- validRound2,
                                            msgsPropose <- msgsPropose2, msgsPrevote <- msgsPrevote2,
                                            msgsPrecommit <- msgsPrecommit2, evidence <- evidence2,
                                            action <- action2, profit <- profit2, rewarded <- rewarded2,
                                            participated <- participated2, numParticipated <- numParticipated2,
                                            rewarddecided <- rewarddecided2

Init == /\ G1!Init
        /\ G2!Init
        /\ rational \in Corr 
        \* /\ rational \in (Corr \ {Proposer[0]})
           
InsertProposal(p) == /\ G1!InsertProposal(p)
                     /\ G2!InsertProposal(p)
                     /\ UNCHANGED <<rational>> 
                     
                     
UponProposalInPropose(p) ==  /\ G1!UponProposalInPropose(p)
                             /\ IF p = rational /\ p /= Proposer[round2[p]]
                                THEN UNCHANGED <<vars2>>
                                ELSE G2!UponProposalInPropose(p)
                             /\ UNCHANGED <<rational>>  
                             
UponProposalInProposeAndPrevote(p) ==  /\ G1!UponProposalInProposeAndPrevote(p)
                                       /\ IF p = rational /\ p /= Proposer[round2[p]]
                                          THEN UNCHANGED <<vars2>>          
                                          ELSE G2!UponProposalInProposeAndPrevote(p)
                                       /\ UNCHANGED <<rational>> 
                                      
UponQuorumOfPrevotesAny(p) ==  /\ G1!UponQuorumOfPrevotesAny(p)
                               /\ IF p = rational /\ p /= Proposer[round2[p]]
                                  THEN UNCHANGED <<vars2>>
                                  ELSE G2!UponQuorumOfPrevotesAny(p)
                               /\ UNCHANGED <<rational>> 
                               
UponProposalInPrevoteOrCommitAndPrevote(p) == /\ G1!UponProposalInPrevoteOrCommitAndPrevote(p)
                                              /\ IF p = rational /\ p /= Proposer[round2[p]]
                                                 THEN UNCHANGED <<vars2>>
                                                 ELSE G2!UponProposalInPrevoteOrCommitAndPrevote(p)
                                              /\ UNCHANGED <<rational>>   
                                              
UponQuorumOfPrecommitsAny(p) ==  /\ G1!UponQuorumOfPrecommitsAny(p)
                                 /\ IF p = rational /\ p /= Proposer[round2[p]]
                                    THEN UNCHANGED <<vars2>>
                                    ELSE G2!UponQuorumOfPrecommitsAny(p)
                                 /\ UNCHANGED <<rational>>   
                
                
UponProposalInPrecommitNoDecision(p) == /\ G1!UponProposalInPrecommitNoDecision(p)
                                        /\ G2!UponProposalInPrecommitNoDecision(p)
                                        /\ UNCHANGED <<rational>>
                                        
                                        
RewardVotersByLeader(p,q) == /\ G1!RewardVotersByLeader(p, q, TRUE)
                             /\ IF p = rational /\ p = Proposer[round2[p]]
                                THEN \/ G2!RewardVotersByLeader(p, q, FALSE) \/ G2!RewardVotersByLeader(p, q, TRUE)
                                ELSE G2!RewardVotersByLeader(p, q, TRUE)
                             /\ UNCHANGED <<rational>>   

Reward(p) == /\ G1!Reward(p)
             /\ G2!Reward(p)
             /\ UNCHANGED <<rational>>
              
RewardVoters(p) == /\ G1!RewardVoters(p)
                   /\ G2!RewardVoters(p)
                   /\ UNCHANGED <<rational>>
             
RewardAll(p) == /\ G1!RewardAll(p)
                /\ G2!RewardAll(p)
                /\ UNCHANGED <<rational>>
             
Termination == /\ G1!AllHaveDecided 
               /\ G1!AllHaveRewarded
               /\ G2!AllHaveDecided
               /\ G2!AllHaveRewarded
           
Next == \E p \in Corr:
            \/ InsertProposal(p)
            \/ UponProposalInPropose(p)
            \/ UponProposalInProposeAndPrevote(p)
            \/ UponQuorumOfPrevotesAny(p)
            \/ UponProposalInPrevoteOrCommitAndPrevote(p)
            \/ UponQuorumOfPrecommitsAny(p)
            \/ UponProposalInPrecommitNoDecision(p)
            \/ \E q \in Corr: RewardVotersByLeader(p, q)
            \/ Reward(p)
        
\*Check == IF Termination
\*         THEN Profit1[Rational]+Merit1[Rational] \geq Profit2[Rational]+Merit2[Rational]
\*         ELSE TRUE
        
\*Equilibrium == IF Termination
\*               THEN \A p \in Corr: profit1[p] \geq profit2[p]
\*               ELSE TRUE
               
Equilibrium == IF Termination
               THEN profit1[rational] \geq profit2[rational]
               ELSE TRUE
               
NotEquilibrium == IF Termination
                  THEN \E p \in Corr: profit2[p] > profit1[p]
                  ELSE TRUE

=============================================================================
\* Modification History
\* Last modified Mon Jun 12 01:41:44 CEST 2023 by 2923277
\* Created Tue Jun 06 11:35:53 CEST 2023 by 2923277
