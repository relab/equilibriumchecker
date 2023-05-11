----------------------------- MODULE Committee -----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Blocks, Processes

VARIABLES Blockchain, Decided, Profit, Merit, NewBlock, Valid

K == 15

R == 10

CCheck == 2

CSend == 1

Init == /\ LET x == CHOOSE x \in Blocks : TRUE
           IN /\ Blockchain = [[b \in Blocks |-> [parent |->b , round|->-1 , signatures |-> {}, leader |-> {}, committed |-> FALSE, decided |-> FALSE]] EXCEPT ![x] = [parent |-> x , round |-> 0 , signatures |-> Processes, committed |-> FALSE, decided |-> FALSE, leader |-> {}]]
              /\ Decided = [p \in Processes |-> TRUE]
              /\ Profit = [p \in Processes |-> 0]
              /\ Merit = [p \in Processes |-> 0]
              /\ NewBlock = x
              /\ LET y == CHOOSE y \in Blocks : y#x
                 IN Valid = [[b \in Blocks |-> TRUE] EXCEPT ![y] = TRUE]
              
EveryOneDecided == /\ \A p \in Processes : Decided[p] = TRUE

LastCommitted == LET b == CHOOSE b \in Blocks : \A b2 \in Blocks : /\ \/ Blockchain[b].round \geq Blockchain[b2].round
                                                                      \/ ~Blockchain[b2].committed
                                                                   /\ Blockchain[b].committed
                 IN b
                 
IsValid(b) == /\ IF Cardinality(Blockchain[b].signatures) \geq 2\**((Cardinality(Processes)-1) \div 3)+1
                 THEN TRUE
                 ELSE FALSE
                 
NewReward(p) == IF p \in Blockchain[NewBlock].signatures
                THEN Profit[p]+R
                ELSE Profit[p]
                
NewRewardLeader(p) == IF p \in Blockchain[NewBlock].leader
                      THEN Profit[p]+R
                      ELSE Profit[p]
                 
RewardAll == /\ Profit' = [p \in Processes |-> Profit[p]+R]

RewardOnlyVoters == /\ Profit' = [p \in Processes |-> NewReward(p)]

RewardOnlyLeader == /\ Profit' = [p \in Processes |-> NewRewardLeader(p)]
                 
Reward(type) == IF type = "Reward All"
                THEN RewardAll
                ELSE IF type = "Reward Voters"
                     THEN RewardOnlyVoters
                     ELSE RewardOnlyLeader
                 
CommitBlock(type) == /\ EveryOneDecided
                     /\ ~Blockchain[NewBlock].decided
                     /\ IF IsValid(NewBlock)
                        THEN /\ Blockchain' = [Blockchain EXCEPT ![NewBlock] = [parent |-> Blockchain[NewBlock].parent , round |->Blockchain[NewBlock].round, committed |-> TRUE, signatures |-> Blockchain[NewBlock].signatures, decided |-> TRUE, leader |-> Blockchain[NewBlock].leader]]
                             /\ IF Cardinality(Blockchain[NewBlock].leader) = 1
                                THEN /\ Reward(type)
                                ELSE /\ Profit' = Profit
                             /\ UNCHANGED <<Decided, NewBlock, Valid, Merit>>
                        ELSE /\ Blockchain' = [Blockchain EXCEPT ![NewBlock] = [parent |-> Blockchain[NewBlock].parent , round |->Blockchain[NewBlock].round, committed |-> FALSE, signatures |-> Blockchain[NewBlock].signatures, decided |-> TRUE, leader |-> Blockchain[NewBlock].leader]]
                             /\ UNCHANGED <<Decided, NewBlock, Profit, Valid, Merit>>
               
BlockDecided == Blockchain[NewBlock].decided

AddNewBlock(p,b) == /\ BlockDecided
                    /\ Blockchain [b].round = -1
                    /\ NewBlock' = b
                    /\ Blockchain' = [Blockchain EXCEPT ![b] = [parent |-> LastCommitted , round |->Blockchain[LastCommitted].round+1, committed |-> FALSE, signatures |-> Blockchain[b].signatures \union {p}, decided |-> FALSE, leader |-> Blockchain[b].leader \union {p}]]
                    /\ Decided' = [[p2 \in Processes |-> FALSE] EXCEPT ![p] = TRUE]
                    /\ Profit' = Profit
                    /\ Valid' = Valid
                    /\ Merit' = Merit
                    \*/\ Decided' = [p2 \in Processes |-> FALSE]
                    
VVote == IF Cardinality(Blockchain[NewBlock].signatures) \geq 2\**((Cardinality(Processes)-1) \div 3)+1
         THEN TRUE
         ELSE FALSE
                                                     
Vote(p,dvo) == /\ ~Decided[p]
               /\ IF dvo
                      THEN /\ Decided' = [Decided EXCEPT ![p] = TRUE]
                           /\ Blockchain' = [Blockchain EXCEPT ![NewBlock] = [parent |-> Blockchain[NewBlock].parent , round |->Blockchain[NewBlock].round, committed |-> Blockchain[NewBlock].committed, signatures |-> Blockchain[NewBlock].signatures \union {p}, decided |-> Blockchain[NewBlock].decided, leader |-> Blockchain[NewBlock].leader]]    
                           /\ Merit' = [Merit EXCEPT ![p] = Merit[p]-CSend]  
                           /\ UNCHANGED <<NewBlock, Valid, Profit>>
                      ELSE /\ Decided' = [Decided EXCEPT ![p] = TRUE]
                           /\ UNCHANGED <<NewBlock, Profit, Blockchain, Valid, Merit>>
                           
ParticipateCorrect(p) == /\ ~Decided[p]
                         /\ IF Valid[NewBlock] 
                            THEN /\ Vote(p,TRUE)
                                 /\ Profit' = [Profit EXCEPT ![p] = Profit[p]-CCheck-CSend]
                            ELSE /\ Vote(p,FALSE)
                                 /\ Profit' = [Profit EXCEPT ![p] = Profit[p]-CCheck]
                         
                               
ParticipateRational(p) == \/ Vote(p,TRUE) /\ Profit' = [Profit EXCEPT ![p] = Profit[p]-CSend]
                          \/ Vote(p,FALSE)
                          
                            
Termination == \A b \in Blocks : Blockchain[b].decided

Validity == \A b \in Blocks : IF Blockchain[b].decided
                              THEN Valid[b]
                              ELSE TRUE
                            
              
Next == \/ CommitBlock(TRUE)
        \/ \E p \in Processes , b \in Blocks : AddNewBlock(p,b)
        \/ \E p \in Processes : ParticipateRational(p)

=============================================================================
\* Modification History
\* Last modified Fri Sep 17 00:27:30 CEST 2021 by SHRservice
\* Created Wed Sep 15 02:34:27 CEST 2021 by SHRservice
