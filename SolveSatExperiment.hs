{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
module Main
  ( main
  )
where

import           Control.Monad                    (forM_, replicateM, when,
                                                   zipWithM_)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.State.Strict
import           Data.Array                       (Array, bounds, listArray,
                                                   (!))
import           Data.List                        (findIndex, inits, tails)
import qualified Data.Map                         as M
import           Data.Maybe                       (fromMaybe)
import qualified Data.Set                         as S
import           Debug.Trace                      (trace)
import           Picosat                          (Solution (..), solve,
                                                   solveAll)
import           System.CPUTime                   (getCPUTime)
import           Test.Hspec

import           Base

type Var = Int
newtype Vec = Vec [Var] deriving (Eq, Show)
type Clause = [Int]

type SetSolution = S.Set Int

class Pick a where
  type P a
  pick :: a -> SetSolution -> P a

instance Pick Vec where
  type P Vec = String
  pick (Vec vars) sol = map l vars
    where l v = if S.member v sol then 'x' else 'o'


data S = S
    { nextId  :: Int
    , clauses :: [Clause]
    }
    deriving (Show)

runS f = runStateT f initialState
evalS f = evalStateT f initialState

-- `1` is reserved as a constantly false variable
initialState = S 2 [[-1]]

falseVar :: Var
falseVar = 1


solutions = do
  cs <- gets clauses
  ls <- lift (solveAll cs)
  return [ xs | Solution xs <- ls ]

setSolution :: StateT S IO SetSolution
setSolution = do
  cs          <- gets clauses
  Solution xs <- lift (solve cs)
  return $ S.fromList xs

allSetSolutionsDo :: (SetSolution -> StateT S IO a) -> StateT S IO ()
allSetSolutionsDo f = do
  cs <- gets clauses
  xs <- lift (solveAll cs)
  forM_ xs $ \(Solution x) -> f (S.fromList x)

allocVars :: Int -> StateT S IO [Var]
allocVars n = do
  first <- gets nextId
  let last = first + n - 1
  modify (\s -> s { nextId = last + 1 })
  return [first .. last]

allocVar :: StateT S IO Var
allocVar = head <$> allocVars 1

exactlyOne :: [Var] -> StateT S IO ()
exactlyOne xs = do
  clause xs
  mapM_ clause [ [-a, -b] | (a : rest) <- tails xs, b <- rest ]

vec :: Int -> StateT S IO Vec
vec n = Vec <$> allocVars n

clause :: [Int] -> StateT S IO ()
clause lits = do
  modify (\s -> s { clauses = lits : clauses s })

dumpClauses = do
  cs <- gets clauses
  lift (mapM_ print cs)




data Pos = BeforeBlock Int
    | InBlock Int Int
    | Done
    | Fail
    deriving (Eq, Show)

buildStates :: [Int] -> [Pos]
buildStates xs = recur xs 0
 where
  recur [] block = [BeforeBlock block]
  recur (x : xs) block =
    (BeforeBlock block : map (InBlock block) [0 .. x - 1])
      ++ recur xs (succ block)

dumpCnfStats = do
  cs <- gets clauses
  let histo = M.fromListWith (+) [ (length c, 1) | c <- cs ]
  lift $ putStrLn
    (  "num clauses: "
    ++ show (length cs)
    ++ "\nnum clauses by size:\n"
    ++ unlines (map (("   " ++) . show) (M.toList histo))
    )


spec = describe "match states" $ do
  fit "can match" $ evalS $ do
    v@(Vec vs) <- vec 6
    walkStates vs [2, 2]
    dumpClauses
    allSetSolutionsDo $ \s -> do
      let r = pick v s
      trace ("cm " ++ show r) (return ())
  it "can match longer" $ evalS $ do
    v@(Vec vs) <- vec 14
    walkStates vs [4, 1, 2, 3]
    -- dumpClauses
    dumpCnfStats
    allSetSolutionsDo $ \s -> do
      let r = pick v s
      trace ("cm " ++ show r) (return ())
      when
        (not
          (      r
          `elem` [ "oxxxxoxoxxoxxx"
                 , "xxxxooxoxxoxxx"
                 , "xxxxoxooxxoxxx"
                 , "xxxxoxoxxooxxx"
                 , "xxxxoxoxxoxxxo"
                 ]
          )
        )
        (error "bad result")



implies a b = do
  clause [-a, b]
  clause [a, -b]

andImplies a b c = do
  clause [-a, -b, c]
  clause [a, -c]
  clause [b, -c]


walkStates :: [Var] -> [Int] -> StateT S IO ()
walkStates fields0 nums = do
  iniv <- allocVar
  clause [iniv]
  -- lift (print ("initial state", iniv))
  finalStates <- recur (fields0 ++ [falseVar]) [(BeforeBlock 0, iniv)]
  clause [ v | (Done, v) <- finalStates ]
  sequence_ [ clause [-v] | (Fail, v) <- finalStates ]
  sequence_ [ clause [-v] | (BeforeBlock _, v) <- finalStates ]
  sequence_ [ clause [-v] | (InBlock _ _, v) <- finalStates ]
 where
  recur []               states = return states
  recur (field : fields) states = do
    -- lift (print ("recur", field, fields))
    nextStates <- mapM (m field) states
    {-lift $ do
        putStrLn ("next states: " ++ show (length (concat nextStates)))
        mapM_ (\x -> putStrLn ("   " ++ show x)) nextStates -}
    recur fields (concat nextStates)

  -- before block
  m field (BeforeBlock n, prev) = do
    -- if field is white we stay in the same state
    wv <- allocVar
    andImplies (-field) prev wv

    -- if field is black we enter the next block state
    bv <- allocVar
    andImplies field prev bv

    return [(BeforeBlock n, wv), (InBlock n 1, bv)]

  -- overrun, one block too much (can this really happen?)
  -- m field (InBlock n p, prev) | n >= length nums = do
  --   clause [-prev]

  -- InBlock, unfinished
  m field (InBlock n p, prev) | p < nums !! n = do
    -- if field is white we fail, our block is unfinished
    clause [field, -prev]

    -- if field is black we step to the next InBlock state
    bv <- allocVar
    andImplies field prev bv

    return [(InBlock n (succ p), bv)]

  -- InBlock, finished
  m field (InBlock n p, prev) | p == nums !! n = do
    -- if field is white we succeed this block, it's finished.
    wv <- allocVar
    andImplies (-field) prev wv

    -- if field is black we fail this block: it's too long.
    clause [-field, -prev]

    return
      [if n == length nums - 1 then (Done, wv) else (BeforeBlock (succ n), wv)]

  m field (Done, prev) = do
    -- if field is white we stay done
    wv <- allocVar
    andImplies (-field) prev wv

    -- if field is black we did overrun
    bv <- allocVar
    clause [-field, -prev]

    return [(Done, wv)]

  -- sticky failure
  m _ (Fail, v) = return [(Fail, v)]



nonogram :: Givens -> StateT S IO Vec
nonogram (Givens w h rowNums colNums) = do
  ar@(Vec fields) <- vec (w * h)
  let array = listArray ((1, 1), (w, h)) fields
  buildConstraints (extractRow array) rowNums w
  buildConstraints (extractCol array) colNums h
  return ar
 where
  buildConstraints extract nums size = zipWithM_ (bc extract size) [1 ..] nums
  bc extract size coord givenNums = do
    let fs = extract coord
    walkStates fs givenNums

extractRow array row = [ array ! (c, row) | c <- [1 .. w] ]
  where (_, (w, _)) = bounds array

extractCol array col = [ array ! (col, r) | r <- [1 .. h] ]
  where (_, (_, h)) = bounds array



main = do
  runS $ do
    let givens = n4
    start    <- lift getCPUTime
    ar       <- nonogram givens
    mid      <- lift getCPUTime
    sol      <- setSolution
    finished <- lift getCPUTime
    let fieldsStr      = pick ar sol
    let Givens w h _ _ = givens
    let fields = listArray
          ((1, 1), (w, h))
          [ if c == 'x' then Black else White | c <- fieldsStr ]
    lift (print (empty givens))
    let board = Board givens fields
    lift (print board)
    lift (print ("encoding ms", fromIntegral (mid - start) / (10 ^ 9)))
    lift (print ("picosat ms", fromIntegral (finished - mid) / (10 ^ 9)))
    dumpCnfStats
  return ()

{-

This variant is a bit slower.
Many states could be fused though...



                1   1
                1 3 4 1 1           1
              3 2 2 2 1 1           1 2 2
              1 1 1 1 2 1 3 4 4 5 5 1 5 1
            5 2 2 1 1 1 1 3 1 1 1 4 1 1 1
        1 1|. B . . . . . B . . . . . . . |
        2 4|. B B . B B B B . . . . . . . |
      1 1 1|. B . B . . . B . . . . . . . |
          5|. . B B B B B . . . . . . . . |
        2 4|. . . B B . . . . . B B B B . |
    1 1 2 1|. . B . B . . . . . B B . B . |
    2 1 4 1|. B B . B . . . . B B B B . B |
    1 1 4 1|B . . B . . . . B B B B . . B |
      1 2 6|B . . B B . . . B B B B B B . |
  1 1 2 2 1|B . B . B B . . B B . . . B . |
1 1 2 1 1 1|B . . B . B B . B . . B . B . |
    2 1 1 1|B B . . . . . B . . . B . B . |
  2 1 1 2 2|. B B . B . . B . . B B . B B |
      2 3 1|. . B B . . . B B B . B . . . |
        3 3|. . . . B B B . . . . . B B B |

("encoding ms",323.538746)
("picosat ms",645.973841)
num clauses: 199142
num clauses by size:
   (1,11828)
   (2,132569)
   (3,54715)
   (11,2)
   (21,2)
   (35,1)
   (45,5)
   (55,2)
   (56,2)
   (70,1)
   (84,1)
   (91,1)
   (120,2)
   (126,4)
   (220,1)
   (286,1)
   (330,3)
   (495,2)
-}
