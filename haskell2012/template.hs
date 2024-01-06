import Data.List
import Data.Maybe

type Id = String

type State = Int

type Transition = ((State, State), Id)

type LTS = [Transition]

type Alphabet = [Id]

data Process = STOP | Ref Id | Prefix Id Process | Choice [Process]
             deriving (Eq, Show)

type ProcessDef = (Id, Process)

type StateMap = [((State, State), State)]

------------------------------------------------------
-- PART I

lookUp :: Eq a => a -> [(a, b)] -> b
--Pre: The item is in the table
lookUp
  = (fromJust .) . lookup

states :: LTS -> [State]
states
  = nub . states'

states' :: LTS -> [State]
states'
  = concatMap (\((a, b),_) -> [a, b])

transitions :: State -> LTS -> [Transition]
transitions s
  = filter ((== s). fst . fst)

alphabet :: LTS -> Alphabet
alphabet
  = nub . map snd

------------------------------------------------------
-- PART II

actions :: Process -> [Id]
actions (Prefix id p)
  = nub (id : actions p)
actions (Choice ps)
  = nub (concatMap actions ps)
actions _
  = []

accepts :: [Id] -> [ProcessDef] -> Bool
--Pre: The first item in the list of process definitions is
--     that of the start process.
accepts ids pdefs@((_, ip) : _)
  = accepts' ids ip
  where
    accepts' :: [Id] -> Process -> Bool
    accepts' ids (Choice ps)
      = or (map (accepts' ids) ps)
    accepts' (id :ids) (Prefix id' p)
      = id == id' && accepts' ids p
    accepts' ids (Ref id')
      = accepts' ids (lookUp id' pdefs)
    accepts' ids _
      = null ids

------------------------------------------------------
-- PART III

composeTransitions :: Transition -> Transition 
                  -> Alphabet -> Alphabet 
                  -> StateMap 
                  -> [Transition]
--Pre: The first alphabet is that of the LTS from which the first transition is
--     drawn; likewise the second.
--Pre: All (four) pairs of source and target states drawn from the two transitions
--     are contained in the given StateMap.
composeTransitions ((s, t), a) ((s', t'), a') alpha1 alpha2 m
  | a == a'                         = [((i (s, s'), i (t, t')), a)]
  | elem a alpha2 && elem a' alpha1 = []
  | elem a' alpha1                  = case1
  | elem a alpha2                   = case2
  | otherwise                       = case1 ++ case2
  where
    case1 = [((i (s, s'), i (t, s')), a)]
    case2 = [((i (s, s'), i (s, t')), a')]

    i :: (State, State) -> State 
    i
      = flip lookUp m

pruneTransitions :: [Transition] -> LTS
pruneTransitions ts
  = nub (visit 0 []) 
  where 
    visit :: State -> [State] -> [Transition]
    visit s ss
      | elem s ss = []
      | otherwise = outgoings ++ concat [visit to (from : ss) | ((from, to), _) <- outgoings]
      where 
        outgoings = transitions s ts
------------------------------------------------------
-- PART IV

compose :: LTS -> LTS -> LTS
compose lts lts'
  = pruneTransitions ts
  where
    alpha  = alphabet lts
    alpha' = alphabet lts'
    cps    = cp (states lts) (states lts')
    cpt    = concat [catchCP s s' (transitions s lts) (transitions s' lts') | (s, s') <- cps]
    ts     = concat [catchComposeTransitions t t' alpha alpha' m | (t, t') <- cpt]
    m      = ((0, 0), 0) : zip (cps \\ [(0, 0)]) [1..]
   
catchCP :: State -> State 
       -> [Transition] -> [Transition]
       -> [(Transition, Transition)]
catchCP s s' [] ts'
  = cp [((s, s), "$")] ts'
catchCP s s' ts []
  = cp ts [((s', s'), "$'")]
catchCP s s' ts ts'
  = cp ts ts'

catchComposeTransitions :: Transition -> Transition
                       -> Alphabet -> Alphabet
                       -> StateMap 
                       -> [Transition]
catchComposeTransitions t t' alpha alpha' m
  = composeTransitions t t' salpha salpha' m
  where 
    salpha  = add "$'" t' alpha
    salpha' = add "$" t alpha'

add :: Id -> Transition -> Alphabet -> Alphabet
add sen (_, id) al
  | sen == id = sen : al
  | otherwise = al

cp :: [a] -> [b] -> [(a, b)]
cp as bs = [(a, b) | a <- as, b <- bs]

------------------------------------------------------
-- PART V

buildLTS :: [ProcessDef] -> LTS
-- Pre: All process references (Ref constructor) have a corresponding
--      definition in the list of ProcessDefs.
buildLTS pdefs@((id, p) : _)
  = lts  
  where 
    (lts, _, _) = buildLTS' 0 1 [(Ref id, 0)] p

    buildLTS' :: State -> State -> [(Process, State)] -> Process -> (LTS, State, [(Process, State)])
    buildLTS' s s' pis p@(Prefix id p')
      | Just s0 <- lookup p pis  = ([((s, s0), id)], s', pis)
      | Just s0 <- lookup p' pis = ([((s, s0), id)], s', (p, s) : pis)
      | otherwise                = (((s, s'), id) : lts', s'', pis')
      where
        (lts', s'', pis') = buildLTS' s' (s' + 1) ((p, s) : pis) p'
    buildLTS' s s' pis p@(Ref id)
      | Just s0 <- lookup p pis = ([((s, s0), id)], s', pis)
      | otherwise               = buildLTS' s s' ((p, s) : pis) p'
      where
        p' = lookUp id pdefs
    buildLTS' s s' pis p@(Choice ps)
      | Just s0 <- lookup p pis = ([], s', pis)
      | otherwise               = foldl (\(lts0, s0, pis0) p -> 
                      let (lts', s', pis') = buildLTS' s s0 pis0 p 
                      in (lts0 ++ lts', s', pis') 
                        ) ([], s', (p, s) : pis) ps
    buildLTS' s s' pis STOP
      = ([], s', pis)

------------------------------------------------------
-- Sample process definitions...

vendor, clock, play, maker, user, p, q, switch, off, on :: ProcessDef

vendor
  = ("VENDOR", Choice [Prefix "red"  (Prefix "coffee" (Ref "VENDOR")),
                       Prefix "blue" (Prefix "tea" (Ref "VENDOR")),
                       Prefix "off" STOP])

clock
  = ("CLOCK", Prefix "tick" (Prefix "tock" (Ref "CLOCK")))

play
  = ("PLAY", Choice [Prefix "think" (Prefix "move" (Ref "PLAY")),
                     Prefix "end" STOP])

maker
  = ("MAKER", Prefix "make" (Prefix "ready" (Ref "MAKER")))

user  
  = ("USER",  Prefix "ready" (Prefix "use" (Ref "USER")))

p = ("P", Prefix "a" (Prefix "b" (Prefix "c" STOP)))

q = ("Q",  Prefix "d" (Prefix "c" (Prefix "b" (Ref "Q"))))

switch
  = ("SWITCH", Ref "OFF")

off
  = ("OFF", Choice [Prefix "on" (Ref "ON")])

on  
  = ("ON",  Choice [Prefix "off" (Ref "OFF")])

------------------------------------------------------
-- Sample LTSs...

vendorLTS, clockLTS, playLTS, clockPlayLTS, makerLTS, userLTS, makerUserLTS,
  pLTS, qLTS, pqLTS, switchLTS :: LTS

vendorLTS
  = [((0,1),"off"),((0,2),"blue"),((0,3),"red"),((2,0),"tea"),((3,0),"coffee")]

clockLTS
  = [((0,1),"tick"),((1,0),"tock")]

playLTS
  = [((0,1),"end"),((0,2),"think"),((2,0),"move")]

clockPlayLTS
  = [((0,1),"end"),((1,4),"tick"),((4,1),"tock"),((0,3),"tick"),
     ((3,4),"end"),((3,0),"tock"),((3,5),"think"),((5,3),"move"),
     ((5,2),"tock"),((2,0),"move"),((2,5),"tick"),((0,2),"think")]

makerLTS
  = [((0,1),"make"),((1,0),"ready")]

userLTS
  = [((0,1),"ready"),((1,0),"use")]

makerUserLTS
  = [((0,2),"make"),((2,1),"ready"),((1,0),"use"),((1,3),"make"),((3,2),"use")]

pLTS
  = [((0,1),"a"),((1,2),"b"),((2,3),"c")]

qLTS
  = [((0,1),"d"),((1,2),"c"),((2,0),"b")]

pqLTS
  = [((0,1),"d"),((1,4),"a"),((0,3),"a"),((3,4),"d")]

switchLTS
  = [((0,1),"on"),((1,0),"off")]

