module DomsMatch where

 {- play a 5's & 3's singles match between 2 given players
    play n games, each game up to 61
 -}
 
 --import Doms
 import System.Random
 import Data.List
 import Debug.Trace
 
 type Dom = (Int,Int)
 -- with highest pip first i.e. (6,1) not (1,6)

 data DomBoard = InitBoard|Board Dom Dom History
                    deriving (Show,Eq)
 
 type History = [(Dom,Player,MoveNum)]
 -- History allows course of game to be reconstructed                                            
                                               
 data Player = P1|P2 -- player 1 or player 2
                  deriving (Eq,Show)
 
 data End = L|R -- left end or right end
                  deriving (Eq,Show)
 
 type MoveNum = Int

 type Hand = [Dom]
  
 -- the full set of Doms
 domSet :: [Dom]
 
 domSet = [(6,6),(6,5),(6,4),(6,3),(6,2),(6,1),(6,0),
                 (5,5),(5,4),(5,3),(5,2),(5,1),(5,0),
                       (4,4),(4,3),(4,2),(4,1),(4,0),
                             (3,3),(3,2),(3,1),(3,0),
                                   (2,2),(2,1),(2,0),
                                         (1,1),(1,0),
                                               (0,0)]
                                                                                         
 
 type Move = (Dom,End)
 type Scores = (Int,Int)
                                                                                              
 -- state in a game - p1's hand, p2's hand, player to drop, current board, scores 
 type GameState =(Hand,Hand,Player, DomBoard, Scores)
 
 
 ------------------------------------------------------
 {- DomsPlayer
    given a Hand, the Board, which Player this is and the current Scores
    returns a Dom and an End
    only called when player is not knocking
    made this a type, so different players can be created
 -}
 
 type DomsPlayer = Hand->DomBoard->Player->Scores->(Dom,End)
 
 --------------------------------------------------------------------
 ------------------ Assignment 3 Implementation ---------------------
 ------------------ Written by Georgica Bors ------------------------
 
 -- Tactic data type --
 type Tactic = Hand->DomBoard-> Player -> Scores -> Maybe(Dom,End)
 
 
 ------------------- Tactics ----------------------------------------
 
 {- firstDrop Tactic -chooses (5,4) as first
  drop on an empty board if (5,4) is present in
  the hand.
  returns maybe (Dom,End)  
  h - hand
  board - current board
  player
  scores
 -}
 firstDrop :: Tactic
 firstDrop h board _ _
    | (board == InitBoard) && (domInHand (5,4) h) = Just (((5,4),L))
    | otherwise = Nothing
 
 
 {- tryToWin Tactic- if player's score is higher than 53
  check if there is a winning dom.
  returns maybe (Dom,End)  
  h - hand
  board - current board
  player - current player
  scores - current scores
 -}
 tryToWin :: Tactic
 tryToWin h board p scores
    | score >= 53 && maybeToBool winner = winner
    | otherwise = Nothing
    where score = getPlayerScore scores p
          winner = checkWinner h board score
 
 {- getTo59 Tactic- if player's score is higher than
  51 try to get to score 59
  returns maybe (Dom,End)  
  h - hand
  board - current board
  player - current player
  scores - current scores
 -}
 getTo59 :: Tactic
 getTo59 [] _ _ _ = Nothing
 getTo59 (h:t) b p scores
    |  score >= 51 && goesLP h b && scoreDom h L b == (59-score) = Just ((h,L))
    |  score >= 51 && goesRP h b && scoreDom h R b == (59-score) = Just ((h,R))
    | otherwise = getTo59 t b p scores
    where score = getPlayerScore scores p
 
 {- makeOpponentKnock Tactic- check if opponent has been 
  knocking in the past by looking at the history. If yes, 
  try to make him knock again.
  returns maybe (Dom,End)  
  hand - current players's hand
  board - current board
  p - current player
  s - current scores
 -} 
 makeOpponentKnock :: Tactic
 makeOpponentKnock _ InitBoard _ _ = Nothing
 makeOpponentKnock hand board@(Board _ _ history) p s
    | maybeToBool pastKnocking  && not(knocking newHand board) && 
                   (isPipAtEdge newBoard pip) && opponentKnocking = Just((dom,end))                                                                
    | otherwise = Nothing 
    where pastKnocking = checkForPastKnocking history p
          pip = resMaybe pastKnocking   
          newHand = possPlaysByPip hand board pip
          (dom,end) = hsdPlayer newHand board p s
          newBoard =  updateBoard dom end p board
          oppHand = opponentPossibleHand newHand newBoard
          opponentKnocking = knocking oppHand newBoard
 
 {- preventOppWin Tactic- if the opp is getting close in the end
  game, look for a dom which will prevent him winning.
  returns maybe (Dom,End)  
  hand - current players's hand
  board - current board
  p - current player
  scores - current scores
 -}
 preventOppWin :: Tactic
 preventOppWin [] _ _ _ = Nothing
 preventOppWin hand@(h:t) board p scores
    | oppScore >= 53 && not(knocking hand board) && not(maybeToBool oppWinner) = Just((dom,end))          
    | oppScore >= 53 && not(knocking newHand board) = preventOppWin newHand board p scores
    | otherwise = Nothing
    where oppScore = getOppScore scores p
          (dom, end) = hsdPlayer hand board p scores
          newBoard = updateBoard dom end p board
          newHand = remove dom hand
          oppHand = opponentPossibleHand newHand newBoard
          oppWinner = checkWinner oppHand newBoard oppScore
          
 {- dangerousDom Tactic- play any double only if it
  can be knocked off.
  returns maybe (Dom,End)  
  hand - current players's hand
  board - current board
  p - current player
  scores - current scores
 -}        
 dangerousDom :: Tactic -- any double is dangerous/ play it only if you can knock it off 
 dangerousDom hand@(h:t) board p s
    | l == r && pipInHand r newHand = Just ((l,r),e)
    | l == r && not (knocking newHand board) = Just (hsdPlayer newHand board p s)
    | otherwise = Just (hsdPlayer hand board p s)
    where ((l,r), e) = hsdPlayer hand board p s
          newHand = remove (l,r) hand
          
 {- majoritySpotValues Tactic- if the
  player has the majority of 1 spot value, play hsd with
  that value.
  returns maybe (Dom,End)  
  hand - current players's hand
  board - current board
  p - current player
  s - current scores
 -}
 majoritySpotValues :: Tactic
 majoritySpotValues hand@(h:t) board p s
    | maybeToBool majoritySpotValue && not(knocking newHand board) 
                                    && isPipAtEdge newBoard spotValue = Just((dom,end))                                                         
    | otherwise = Nothing 
    where majoritySpotValue = getMajoritySpotValues hand board 6
          spotValue = resMaybe majoritySpotValue
          newHand = [d | d<- hand, let (l,r) = d, l == spotValue || r == spotValue]
          (dom, end) = hsdPlayer newHand board p s
          newBoard =  updateBoard dom end p board 
 
 {- hsdRiskyDom Tactic- play hsd unless it risks
 the opponent scoring more.
  returns maybe (Dom,End)  
  hand - current players's hand
  board - current board
  p - current player
  s - current scores
 -}
 hsdRiskyDom :: Tactic
 hsdRiskyDom hand@(h:t) board p s
    | opponentCanPlay && currentScore >= opponentScore = Just((dom,end))
    | opponentCanPlay &&(currentScore < opponentScore) && 
            (not (knocking newHand board))= hsdRiskyDom newHand board p s
    | otherwise = Nothing
     where 
           (dom,end) = hsdPlayer hand board p s
           newHand = remove dom hand
           newBoard = updateBoard dom end p board
           currentScore = scoreboard newBoard
           opponentHand = opponentPossibleHand hand board
           opponentCanPlay = not(knocking opponentHand newBoard)
           opponentDom@(d,e) = hsdPlayer opponentHand newBoard p s
           opponentScore = scoreDom d e newBoard
           
 ----------------------------------------------------------------------
 ----------------- Helper Functions -----------------------------------
 
  {- returns the score of the
  current player
  scores 
  player
  -}
 getPlayerScore :: Scores -> Player -> Int
 getPlayerScore (s1, _) P1 = s1
 getPlayerScore (_,s2) P2 = s2
 
  {- checks if there is winning dom
  in the hand, if yes returns it.
  hand
  board
  score
  -}
 checkWinner :: Hand -> DomBoard -> Int -> Maybe (Dom, End)
 checkWinner [] _  _ = Nothing
 checkWinner (h:t) b score
    | goesLP h b && scoreDom h L b == (61-score) = Just ((h,L))
    | goesRP h b && scoreDom h R b == (61-score) = Just ((h,R))
    | otherwise = checkWinner t b score
   
 {- checks if opponent has been knocking
 in the past, if yes it returns the pip value on which
 the opp was knocking on.
  history
  player
  -}
 checkForPastKnocking :: History -> Player -> Maybe Int
 checkForPastKnocking [elem] _ = Nothing
 checkForPastKnocking (h:t) p
    | p1 == p2 && p2 == p = Just (pip)
    | otherwise = checkForPastKnocking t p
    where (d1,p1,_) = h
          (d2,p2,_) = head t
          (_, pip) = d1
 
 {- returns all poss plays with a specific
 pip value.
  hand
  board
  pip value
  -}
 possPlaysByPip :: Hand -> DomBoard -> Int -> Hand
 possPlaysByPip hand board pip = [d | d <- hand, 
                                      let (l,r) = d, 
                                      l==pip || r==pip, 
                                      goesLP d board || goesRP d board]
 
 {- checks if the pip value is at the
 edge of the board.
  board
  pip value
  -}
 isPipAtEdge :: DomBoard -> Int -> Bool
 isPipAtEdge b pip = (getBoardLeftEnd b == pip || getBoardRightEnd b == pip)
 
 {- returns the score of the
  opponent.
  scores
  player
  -}        
 getOppScore :: Scores -> Player -> Int
 getOppScore (_,s2) P1 = s2
 getOppScore (s1,_) P2 = s1

 {- returns the board's 
  left end pip
  board
  -}        
 getBoardLeftEnd :: DomBoard -> Int
 getBoardLeftEnd (Board (l,r) _ _ )  = l 

  {- returns the board's 
  right end pip
  board
  -}   
 getBoardRightEnd :: DomBoard -> Int
 getBoardRightEnd (Board _ (l,r) _) = r
   
 {- checks if one hand contains the majority
  of doms of one spot value. If yes returns 
  that value.
  hand
  board
  pipvalue
  -}
 getMajoritySpotValues :: Hand -> DomBoard -> Int -> Maybe Int
 getMajoritySpotValues _ _ (4) = Nothing
 getMajoritySpotValues hand board spot
    | isMajoritySpotValues hand board spot = Just (spot)
    | otherwise = getMajoritySpotValues hand board (spot-1)
 
 {- returns the number of doms that contain 1 
  pip value.
  pipvalue
  hand
  -}
 numberOfOneSpotValue :: Int -> Hand -> Int
 numberOfOneSpotValue spot hand = length [x | x <- hand, 
                                              let (l,r) = x, 
                                              l==spot || r == spot]
 
 {- checks if one hand has the majority of doms of
  one spot value.
  hand
  board
  pipvalue
  -}
 isMajoritySpotValues :: Hand -> DomBoard -> Int -> Bool
 isMajoritySpotValues hand InitBoard pip
    | pipInHand pip hand  =  numberOfOneSpotValue pip hand > 3
    | otherwise = False
 isMajoritySpotValues hand (Board _ _ history) pip
    | pipInHand pip hand  = (numberOfOneSpotValue pip hand + spotOnBoard) > 3 -- make this a constant                            
    | otherwise = False
    where domsOnBoard = (map (\(d,p,l) -> d) history)
          spotOnBoard = numberOfOneSpotValue pip domsOnBoard
 
 {- removes an element from a list
  elem
  list of elements
  -}
 remove :: Eq a => a -> [a] -> [a]
 remove elem lis = [x|x<-lis, x/= elem]
 
 
  {- returns a hand with all possible doms 
  that can be present in opponent's hand.
  hand
  board
  -}
 opponentPossibleHand :: Hand -> DomBoard -> Hand
 opponentPossibleHand hand InitBoard = [d | d<-domSet, not(domInHand d hand)]
 opponentPossibleHand hand (Board _ _ history) = [d | d<-domSet, 
                                            not(domInHand d hand), 
                                            not(domInHistory d history)]
 {- checks if a dom has been played already
  by looking at the history.
  dom
  history
  -}
 domInHistory :: Dom -> History -> Bool
 domInHistory dom [] = False
 domInHistory dom history = not (null [x | x<-history,
                                      let (d,_,_) = x, 
                                            dom == d])
 
 {- checks if a pip value is present in 
  the hand.
  pipvalue
  hand
  -}
 pipInHand :: Int -> Hand -> Bool
 pipInHand _ [] = False
 pipInHand pip (h:t)
    | (pip == leftPips || pip == rightPips) = True 
    | otherwise = pipInHand pip t
    where (leftPips,rightPips) = h
       
 {- checks if a domino is present in 
  the hand.
  dom
  hand
  -}        
 domInHand :: Dom -> Hand -> Bool
 domInHand _ [] = False
 domInHand domino (h:t)
    | (dl == leftPips && dr == rightPips) = True 
    | (dl == rightPips && dr == leftPips) = True
    | otherwise = domInHand domino t
    where (leftPips,rightPips) = h
          (dl,dr) = domino
 
 {- extract result from a 
 successful Maybe.
 -}
 resMaybe :: (Maybe a) -> a
 resMaybe (Just x) = x
 
 {- converts a maybe type
  to a boolean. This is used to check
  if a tactic has triggered.
 -}
 maybeToBool :: Maybe a -> Bool
 maybeToBool (Just x) = True
 maybeToBool Nothing  = False
 ----------------------------------------------------------------------
 ---------------------- Run Tactics Helper Function -------------------
 {- runTactics
  takes a list of tactics and goes through
  all of them until one tactic triggers.
  If none of them triggers hsd player is called.
  tactics 
  hand
  board
  player
  scores
 -}
 runTactics :: [Tactic] -> Hand -> DomBoard-> Player->Scores->(Dom,End)
 runTactics [] h b p s = hsdPlayer h b p s
 runTactics (h:t) hand b p s
    | maybeToBool tacticResult = resMaybe(tacticResult)
    | otherwise = runTactics t hand b p s
    where tacticResult = h hand b p s
    
 --------------------------------------------------
 ---------------  PLAYERS  ------------------------
 --------------------------------------------------
 {- a player consists of a list of tactics. 
  It calls runTactics to go trough all tactics from
  that list.
  -}
 firstPlayer :: DomsPlayer
 firstPlayer h b p s = runTactics tactics h b p s
                    where tactics = [firstDrop]
                    
 secondPlayer :: DomsPlayer
 secondPlayer h b p s = runTactics tactics h b p s
                    where tactics = [tryToWin, firstDrop]
 
 thirdPlayer :: DomsPlayer
 thirdPlayer h b p s = runTactics tactics h b p s
                    where tactics = [tryToWin, getTo59,firstDrop]
                    
 fourthPlayer :: DomsPlayer
 fourthPlayer h b p s = runTactics tactics h b p s
                    where tactics = [tryToWin,preventOppWin, getTo59,firstDrop ]
                    
 fifthPlayer :: DomsPlayer
 fifthPlayer h b p s = runTactics tactics h b p s
                    where tactics = [tryToWin,preventOppWin, getTo59,firstDrop, hsdRiskyDom]
                    
 sixthPlayer :: DomsPlayer
 sixthPlayer h b p s = runTactics tactics h b p s
                    where tactics = [tryToWin,preventOppWin, getTo59,firstDrop, hsdRiskyDom, makeOpponentKnock]
                    
 seventhPlayer :: DomsPlayer
 seventhPlayer h b p s = runTactics tactics h b p s
                    where tactics = [tryToWin,preventOppWin, getTo59,firstDrop, hsdRiskyDom, dangerousDom]
                    
 eighthPlayer :: DomsPlayer
 eighthPlayer h b p s = runTactics tactics h b p s
                    where tactics = [tryToWin,preventOppWin, getTo59,firstDrop, hsdRiskyDom, majoritySpotValues]
 
 ---------------------------------------------------------------------------------
 ------------------ End of Assignment 3 implementation ---------------------------
 ---------------------------------------------------------------------------------
 
 {- variables
     hand h
     board b
     player p
     scores s
 -}

 -- example players
 -- randomPlayer plays the first legal dom it can, even if it goes bust
 randomPlayer :: DomsPlayer
 
 randomPlayer h b p s 
  |not(null ldrops) = ((head ldrops),L)
  |otherwise = ((head rdrops),R)
  where
   ldrops = leftdrops h b
   rdrops = rightdrops h b
   
 -- hsdplayer plays highest scoring dom
 -- we have  hsd :: Hand->DomBoard->(Dom,End,Int)
 
 hsdPlayer h b p s = (d,e)
                     where (d,e,_)=hsd h b
                     
  -- highest scoring dom

 hsd :: Hand->DomBoard->(Dom,End,Int)
 
 hsd h InitBoard = (md,L,ms)
  where
   dscores = zip h (map (\ (d1,d2)->score53 (d1+d2)) h)
   (md,ms) = maximumBy (comparing snd) dscores
   
 
 hsd h b = 
   let
    ld=  leftdrops h b
    rd = rightdrops h b
    lscores = zip ld (map (\d->(scoreDom d L b)) ld) -- [(Dom, score)]
    rscores = zip rd (map (\d->(scoreDom d R b)) rd)
    (lb,ls) = if (not(null lscores)) then (maximumBy (comparing snd) lscores) else ((0,0),-1) -- can't be chosen
    (rb,rs) = if (not(null rscores)) then (maximumBy (comparing snd) rscores) else ((0,0),-1)
   in
    if (ls>rs) then (lb,L,ls) else (rb,R,rs)
 
 
                                               
 -----------------------------------------------------------------------------------------
 {- top level fn
    args: 2 players (p1, p2), number of games (n), random number seed (seed)
    returns: number of games won by player 1 & player 2
    calls playDomsGames giving it n, initial score in games and random no gen
 -} 
 
 domsMatch :: DomsPlayer->DomsPlayer->Int->Int->(Int,Int)
 
 domsMatch p1 p2 n seed = playDomsGames p1 p2 n (0,0) (mkStdGen seed)
 
 -----------------------------------------------------------------------------------------
 
{- playDomsGames plays n games

  p1,p2 players
  (s1,s2) their scores
  gen random generator
-}
 
 playDomsGames :: DomsPlayer->DomsPlayer->Int->(Int,Int)->StdGen->(Int,Int)
 
 playDomsGames _ _ 0 score_in_games _ = score_in_games -- stop when n games played
 
 playDomsGames p1 p2 n (s1,s2) gen 
   |gameres==P1 = playDomsGames p1 p2 (n-1) (s1+1,s2) gen2 -- p1 won
   |otherwise = playDomsGames p1 p2 (n-1) (s1,s2+1) gen2 -- p2 won
  where
   (gen1,gen2)=split gen -- get 2 generators, so doms can be reshuffled for next hand
   gameres = playDomsGame p1 p2 (if (odd n) then P1 else P2) (0,0) gen1 -- play next game p1 drops if n odd else p2
 
 -----------------------------------------------------------------------------------------
 -- playDomsGame plays a single game - 61 up
 -- returns winner - P1 or P2
 -- the Bool pdrop is true if it's p1 to drop
 -- pdrop alternates between games
 
 playDomsGame :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->Player
 
 playDomsGame p1 p2 pdrop scores gen 
  |s1==61 = P1
  |s2==61 = P2
  |otherwise = playDomsGame p1 p2 (if (pdrop==P1) then P2 else P1) (s1,s2) gen2
  where
   (gen1,gen2)=split gen
   (s1,s2)=playDomsHand p1 p2 pdrop scores gen1  
  
 -----------------------------------------------------------------------------------------
 -- play a single hand
  
 playDomsHand :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->(Int,Int)
 
 playDomsHand p1 p2 nextplayer scores gen = 
   playDoms p1 p2 init_gamestate
  where
   spack = shuffleDoms gen
   p1_hand = take 9 spack
   p2_hand = take 9 (drop 9 spack)
   init_gamestate = (p1_hand,p2_hand,nextplayer,InitBoard,scores) 
   
 ------------------------------------------------------------------------------------------   
 -- shuffle 
 
 shuffleDoms :: StdGen -> [Dom]

 shuffleDoms gen =  
  let
    weights = take 28 (randoms gen :: [Int])
    dset = (map fst (sortBy  
               (\ (_,w1)(_,w2)  -> (compare w1 w2)) 
               (zip domSet weights)))
  in
   dset
   
 ------------------------------------------------------------------------------------------
 -- playDoms runs the hand
 -- returns scores at the end

 
 playDoms :: DomsPlayer->DomsPlayer->GameState->(Int,Int)
 
 playDoms _ _ (_,_,_,_, (61,s2)) = (61,s2) --p1 has won the game
 playDoms _ _ (_,_,_,_, (s1,61)) = (s1,61) --p2 has won the game
 
 
 playDoms p1 p2 gs@(h1,h2,nextplayer,b,scores)
  |(kp1 &&  kp2) = scores -- both players knocking, end of the hand
  |((nextplayer==P1) && (not kp1)) =  playDoms p1 p2 (p1play p1 gs) -- p1 plays, returning new gameState. p2 to go next
  |(nextplayer==P1) = playDoms p1 p2 (p2play p2 gs) -- p1 knocking so p2 plays
  |(not kp2) = playDoms p1 p2 (p2play p2 gs) -- p2 plays
  |otherwise = playDoms p1 p2 (p1play p1 gs) -- p2 knocking so p1 plays
  where
   kp1 = knocking h1 b -- true if p1 knocking
   kp2 = knocking h2 b -- true if p2 knocking
   
 ------------------------------------------------------------------------------------------
 -- is a player knocking?

 knocking :: Hand->DomBoard->Bool
 
 knocking h b = 
  ((null (leftdrops h b)) && (null (rightdrops h b))) -- leftdrops & rightdrops in doms.hs
 
 ------------------------------------------------------------------------------------------
   
 -- player p1 to drop
 
 p1play :: DomsPlayer->GameState->GameState
 
 p1play p1 (h1,h2,_,b, (s1,s2)) = 
  ((delete dom h1), h2, P2,(updateBoard dom end P1 b), (ns1, s2))
   where
    (dom,end) = p1 h1 b P1 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
    score = s1+ (scoreDom dom end b) -- what it scored
    ns1 = if (score >61) then s1 else score -- check for going bust
    
 
 -- p2 to drop
   
 p2play :: DomsPlayer->GameState->GameState
 
 p2play p2 (h1,h2,_,b,(s1,s2)) = 
  (h1, (delete dom h2),P1, (updateBoard dom end P2 b), (s1, ns2))
  where
   (dom,end) = p2 h2 b P2 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
   score = s2+ (scoreDom dom end b) -- what it scored
   ns2 = if (score >61) then s2 else score -- check for going bust
 
   -------------------------------------------------------------------------------------------
 -- updateBoard 
 -- update the board after a play
 
 updateBoard :: Dom->End->Player->DomBoard->DomBoard
 
 updateBoard d e p b
  |e==L = playleft p d b
  |otherwise = playright p d b

  ------------------------------------------------------------------------------------------
 -- doms which will go left
 leftdrops :: Hand->DomBoard->Hand
 
 leftdrops h b = filter (\d -> goesLP d b) h
 
 -- doms which go right
 rightdrops :: Hand->DomBoard->Hand
 
 rightdrops h b = filter (\d -> goesRP d b) h 
 
 -------------------------------------------------
 -- 5s and 3s score for a number
  
 score53 :: Int->Int
 score53 n = 
  let 
   s3 = if (rem n 3)==0 then (quot n 3) else 0
   s5 = if (rem n 5)==0 then (quot n 5) else 0 
  in
   s3+s5
   
 ------------------------------------------------ 
 -- need comparing
 -- useful fn specifying what we want to compare by
 comparing :: Ord b=>(a->b)->a->a->Ordering
 comparing f l r = compare (f l) (f r)
 
 ------------------------------------------------
 -- scoreDom
 -- what will a given Dom score at a given end?
 -- assuming it goes
 
 scoreDom :: Dom->End->DomBoard->Int
 
 scoreDom d e b = scoreboard nb
                  where
                  (Just nb) = (playDom P1 d e b) -- player doesn't matter
 
 ----------------------------------------------------                 
 -- play to left - it will go
 playleft :: Player->Dom->DomBoard->DomBoard
 
 playleft p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playleft p (d1,d2) (Board (l1,l2) r h)
  |d1==l1 = Board (d2,d1) r (((d2,d1),p,n+1):h)
  |otherwise =Board (d1,d2) r (((d1,d2),p,n+1):h)
  where
    n = maximum [m |(_,_,m)<-h] -- next drop number
    
 -- play to right
 playright :: Player->Dom->DomBoard->DomBoard
 
 playright p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playright p (d1,d2)(Board l (r1,r2) h)
  |d1==r2 = Board l (d1,d2) (h++[((d1,d2),p,n+1)])
  |otherwise = Board l (d2,d1) (h++[((d2,d1),p,n+1)])
  where 
    n = maximum [m |(_,_,m)<-h] -- next drop number
 
 ------------------------------------------------------
 -- predicate - will given domino go at left?
 -- assumes a dom has been played
 
 goesLP :: Dom->DomBoard->Bool
 
 goesLP _ InitBoard = True
 
 goesLP (d1,d2) (Board (l,_) _ _) = (l==d1)||(l==d2)


 -- will dom go to the right?
 -- assumes a dom has been played
 
 goesRP :: Dom->DomBoard->Bool
 
 goesRP _ InitBoard = True
 
 goesRP (d1,d2) (Board _ (_,r) _) = (r==d1)||(r==d2)
 
 ------------------------------------------------

 -- playDom
 -- given player plays
 -- play a dom at left or right, if it will go

 
 playDom :: Player->Dom->End->DomBoard->Maybe DomBoard
 
 playDom p d L b
   |goesLP d b = Just (playleft p d b)
   |otherwise = Nothing
 
 playDom p d R b
   |goesRP d b = Just (playright p d b)
   |otherwise = Nothing
   
 ---------------------------------------------------    
 -- 5s & threes score for a board
 
 scoreboard :: DomBoard -> Int
 
 scoreboard InitBoard = 0

 scoreboard (Board (l1,l2) (r1,r2) hist)
  |length hist == 1 = score53 (l1+l2) -- 1 dom played, it's both left and right end
  |otherwise = score53 ((if l1==l2 then 2*l1 else l1)+ (if r1==r2 then 2*r2 else r2))
 
 
 