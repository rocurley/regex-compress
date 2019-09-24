import Control.Monad
import Data.List
import Data.Ord
import Safe
import qualified Data.IntMap.Strict as Map
import Data.IntMap.Strict (IntMap)

data RE
    = Star RE
    | And RE RE
    | Or RE RE
    | Wildcard
    | Lit Char
    deriving (Show, Ord, Eq)
data PRE
    = PStar PRE
    | PAnd PRE PRE
    | POr PRE PRE
    | PWildcard
    | PLit Char
    | Seed
    deriving (Show, Ord, Eq)

reify :: PRE -> RE
reify (PStar x) = Star $ reify x
reify (PAnd x y) = And (reify x) (reify y)
reify (POr x y) = Or (reify x) (reify y)
reify PWildcard = Wildcard
reify (PLit c) = Lit c
reify Seed = Star Wildcard

dumbExpand :: PRE -> [PRE]
dumbExpand (PStar x) = PStar <$> dumbExpand x
dumbExpand (PAnd x y) = (PAnd <$> dumbExpand x <*> pure y) ++ (PAnd <$> pure x <*> dumbExpand y)
dumbExpand (POr x y) = (POr <$> dumbExpand x <*> pure y) ++ (POr <$> pure x <*> dumbExpand y)
dumbExpand Seed =
    [PLit c | c <- ['a'..'z']] ++
    [ PWildcard
    , PAnd Seed Seed
    , POr Seed Seed
    , PStar Seed
    ]
dumbExpand _ = []

data REContext
    = CStar
    | CLAnd RE
    | CRAnd RE
    | CLOr RE
    | CROr RE
    deriving (Show, Ord, Eq)
data RELeaf
    = LLit Char
    | LWildcard
    deriving (Show, Ord, Eq)

data REZipper = REZipper [REContext] RELeaf
    deriving (Show, Ord, Eq)

applyContext ::  RE -> REContext -> RE
applyContext x CStar = Star x
applyContext l (CLAnd r) = And l r
applyContext r (CRAnd l) = And l r
applyContext l (CLOr r) = Or l r
applyContext r (CROr l) = Or l r

unzip :: REZipper -> RE
unzip (REZipper contextStack (LLit c)) = foldl applyContext (Lit c) contextStack
unzip (REZipper contextStack LWildcard) = foldl applyContext Wildcard contextStack

data Trace
    = LitMatch
    | WildcardMatch Char
    | StarEnter
    | StarSkip
    | OrLeft
    | OrRight
    deriving (Show, Ord, Eq)

wrapZipper :: [REContext] -> (REZipper, [Trace]) -> (REZipper, [Trace])
wrapZipper wrapper ((REZipper ctx leaf), trace) = (REZipper (ctx++wrapper) leaf, trace)

pushTrace :: Trace -> [(REZipper, [Trace])] -> [(REZipper, [Trace])]
pushTrace tr = map (\ (z, trs) -> (z, tr:trs))

concatTrace :: [Trace] -> [(REZipper, [Trace])] -> [(REZipper, [Trace])]
concatTrace prior = map (\ (z, new) -> (z, prior ++ new))

first :: RE -> [(REZipper, [Trace])]
first = first' [] where
    first' :: [REContext] -> RE -> [(REZipper, [Trace])]
    first' acc (Star re) = advance' (CStar: acc) re
    first' acc (And l r) = first' (CLAnd r: acc) l
    first' acc (Or l r) = pushTrace OrLeft (first' (CLOr r: acc) l)
                        ++ pushTrace OrRight (first' (CROr l: acc) r)
    first' acc Wildcard = pure (REZipper acc LWildcard, [])
    first' acc (Lit c) = pure (REZipper acc $ LLit c, [])

advance :: REZipper -> [(REZipper, [Trace])]
advance (REZipper ctx LWildcard) = advance' ctx Wildcard
advance (REZipper ctx (LLit c)) = advance' ctx  $ Lit c

advance' :: [REContext] -> RE -> [(REZipper, [Trace])]
advance' [] _ = []
advance' (CStar:ctx) re = let
    continue = pushTrace StarSkip $ advance' ctx (Star re)
    restart = pushTrace StarEnter $ wrapZipper (CStar:ctx) <$> first re
    in continue ++ restart
advance' (CLAnd r:ctx) l = wrapZipper (CRAnd l:ctx) <$> first r
advance' (CRAnd l:ctx) r = advance' ctx $ And l r
advance' (CLOr r:ctx) l = advance' ctx $ Or l r
advance' (CROr l:ctx) r = advance' ctx $ Or l r

step :: Char -> (REZipper, [Trace]) -> [(REZipper, [Trace])]
step c (z@(REZipper _ (LLit cRE)), trs) = guard (c == cRE) >> concatTrace trs (pushTrace LitMatch $ advance z)
step c (z@(REZipper _ LWildcard), trs) = concatTrace trs (pushTrace (WildcardMatch c) $ advance z)

isTerminal :: REZipper -> Bool
isTerminal (REZipper ctx _) = all isTerminal' ctx where
    isTerminal' (CLAnd _) = False
    isTerminal' _ = True

matches :: RE -> String -> [[Trace]]
matches = matches' . first where
    matches' :: [(REZipper, [Trace])] -> String -> [[Trace]]
    matches' zs [] = []
    matches' zs [c] = matchesFinal =<< zs where
        matchesFinal :: (REZipper, [Trace]) -> [[Trace]]
        matchesFinal (z@(REZipper _ LWildcard), tr) = guard (isTerminal z) >> [tr ++ [WildcardMatch c] ]
        matchesFinal (z@(REZipper _ (LLit cRE)), tr) = guard (isTerminal z && c == cRE) >> [tr ++ [LitMatch]]
    matches' zs (c:cs) = matches' (zs >>= step c) cs

reComplexity :: RE -> Int
reComplexity = go 0 where
    go n (Star r) = go (n+1) r
    go n (And l r) = go (go (n+1) l) r
    go n (Or l r) = go (go (n+1) l) r
    go n (Wildcard) = n+1
    go n (Lit _) = n+1

preComplexity :: PRE -> Int
preComplexity = go 0 where
    go n (PStar r) = go (n+1) r
    go n (PAnd l r) = go (go (n+1) l) r
    go n (POr l r) = go (go (n+1) l) r
    go n PWildcard = n+1
    go n (PLit _) = n+1
    go n Seed = n+1

traceComplexity :: [Trace] -> Int
traceComplexity = length

complexity :: RE -> [Trace] -> Int
complexity re tr = reComplexity re + traceComplexity tr

bestMatch :: RE -> String -> Maybe [Trace]
bestMatch re str = minimumByMay (comparing traceComplexity) $ matches re str

pushMatch :: String -> PRE -> IntMap [(PRE, [Trace])] -> IntMap [(PRE, [Trace])]
pushMatch str r = case bestMatch (reify r) str of
    Nothing -> id
    Just tr -> Map.insertWith (++)
        (preComplexity r)
        [(r, tr)]

allMatching :: String -> [(Int, RE, [Trace])]
allMatching str = go $ pushMatch str Seed Map.empty where
    go m = let
        ((preComplexity, best), m') = Map.deleteFindMin m
        new = best >>= (\ (re, _) -> dumbExpand re)
        in map (\ (pre, tr) -> (preComplexity, reify pre, tr)) best
            ++ go (foldr (pushMatch str) m' new)

findBest :: [(Int, RE, [Trace])] -> (Int, RE, [Trace])
findBest ((_, re, tr):rest) = go (complexity re  tr, re, tr) rest where
    go best@(bestComplexity, _, _) ((preComplexity, re, tr): rest) =
        if preComplexity < bestComplexity
        then let
            c = complexity re tr
            in if c < bestComplexity
            then go (c, re, tr) rest
            else go best rest
        else best

main = do
  print $ findBest $ allMatching "aa"

--traverse print $ take 100 $ allMatching "ababab"


