{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Main
  ( main
  )
where

import           Picosat                        ( solve
                                                , solveAll
                                                , Solution(..)
                                                )
import           Control.Monad                  ( forM_
                                                , when
                                                , zipWithM_
                                                , replicateM
                                                )
import           Control.Monad.Trans.State.Strict
import           Control.Monad.Trans.Class      ( lift )
import           Data.List                      ( tails
                                                , inits
                                                , findIndex
                                                )
import           Test.Hspec
import qualified Data.Set                      as S
import           Data.Maybe                     ( fromMaybe )
import           Debug.Trace                    ( trace )
import           Data.Array                     ( Array
                                                , listArray
                                                , (!)
                                                , bounds
                                                )

import           Base

type Var = Int
newtype Number = Number [Var] deriving (Eq, Show)
newtype Arena = Arena [Var] deriving (Eq, Show)
type Clause = [Int]

type SetSolution = S.Set Int

class Pick a where
  type P a
  pick :: a -> SetSolution -> P a

instance Pick Number where
  type P Number = Int
  pick (Number vars) sol =
    fromMaybe (error "bad") (findIndex (flip S.member sol) vars)

instance Pick Arena where
  type P Arena = String
  pick (Arena vars) sol = map l vars
    where l v = if S.member v sol then 'x' else 'o'


data S = S
  { nextId :: Int
  , clauses :: [Clause] }
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

-- a one-hot "decoded" number
number :: Int -> StateT S IO Number
number n = do
  num <- allocVars n
  exactlyOne num
  return (Number num)

boolToNumber :: Var -> StateT S IO Number
boolToNumber x = do
  num@(Number [zero, one]) <- number 2
  clause [x, zero]
  clause [-x, one]
  clause [zero, one]
  clause [-zero, -one]
  return num

exactlyOne :: [Var] -> StateT S IO ()
exactlyOne xs = do
  clause xs
  mapM_ clause [ [-a, -b] | (a : rest) <- tails xs, b <- rest ]

arena :: Int -> StateT S IO Arena
arena n = Arena <$> allocVars n

clause :: [Int] -> StateT S IO ()
clause lits = do
  modify (\s -> s { clauses = lits : clauses s })

dumpClauses = do
  cs <- gets clauses
  lift (mapM_ print cs)

lessThanConstraint :: Number -> Number -> StateT S IO ()
lessThanConstraint (Number xs) (Number ys) =
  mapM_ clause [ [-x, -y] | (x, yt) <- zip xs (tail (inits ys)), y <- yt ]

allFalse = mapM_ (\x -> clause [-x])

blockConstraint :: Number -> Int -> Arena -> StateT S IO ()
blockConstraint start@(Number startVars) len (Arena arena) = do
  let (sa, sb) = splitAt (length startVars - len + 1) startVars
  allFalse sb
  sequence_
    [ pr st 0 (take (len + 2) ar)
    | (st, ar) <- zip sa (tails ([falseVar] ++ arena ++ [falseVar]))
    ]
 where
  pr _ i _ | i == len + 2                   = return ()
  pr st i (r : rs) | i == 0 || i == len + 1 = do
    clause [-st, -r]
    pr st (succ i) rs
  pr st i (r : rs) = do
    clause [-st, r]
    pr st (succ i) rs


nonogram :: Givens -> StateT S IO Arena
nonogram (Givens w h rowNums colNums) = do
  ar@(Arena fields) <- arena (w * h)
  let array = listArray ((1, 1), (w, h)) fields
  buildConstraints (extractRow array) rowNums w
  buildConstraints (extractCol array) colNums h
  return ar
 where
  buildConstraints extract nums size = zipWithM_ (bc extract size) [1 ..] nums
  bc extract size coord givenNums = do
    -- allocate a "start position" for every given number
    startPositions <- replicateM (length givenNums) (number size)
    growingList startPositions
    let fs = extract coord
    zipWithM_ (\start givenNum -> blockConstraint start givenNum (Arena fs))
              startPositions
              givenNums
    let s = sum givenNums
    cardinality (Arena fs) s

extractRow array row = [ array ! (c, row) | c <- [1 .. w] ]
  where (_, (w, _)) = bounds array

extractCol array col = [ array ! (col, r) | r <- [1 .. h] ]
  where (_, (_, h)) = bounds array

-- | every list element is smaller than the next one
growingList :: [Number] -> StateT S IO ()
growingList xs = zipWithM_ lessThanConstraint xs (tail xs)

cardinality (Arena xs) n = do
  numbers <- mapM boolToNumber xs
  count   <- foldTree addNumbers numbers
  numberEqual count n

numberEqual :: Number -> Int -> StateT S IO ()
numberEqual (Number xs) n = clause [xs !! n]


addNumbers (Number xs) (Number ys) = do
  let resLength = length xs + length ys - 1
  res@(Number reslist) <- number resLength
  let resary = listArray (0, resLength - 1) reslist
  -- one implication clause for every possible combination of numbers
  sequence_
    [ clause [-x, -y, resary ! (xnum + ynum)]
    -- a&b -> c
    -- -(a&b) v c
    -- -a v -b v c    
    | (x, xnum) <- zip xs [0 ..]
    , (y, ynum) <- zip ys [0 ..]
    ]
  return res

foldTree :: (a -> a -> StateT S IO a) -> [a] -> StateT S IO a
foldTree _ [x] = return x
foldTree f xs  = pass xs >>= foldTree f
 where
  pass (a : b : rest) = do
    e  <- f a b
    ee <- pass rest
    return (e : ee)
  pass x = return x


data T a = T (T a) (T a) | L a deriving (Show)
test = foldTree (\a b -> return (T a b)) (map L [3, 4, 5, 6, 78])

spec = describe "solve sat" $ do
  it "can alloc vars" $ do
    let lim = 5
    r <- evalS $ do
      a <- number lim
      s <- setSolution
      return (pick a s)
    (r >= 0 && r < lim) `shouldBe` True

  it "can alloc vars 2" $ do
    let lim = 30
    evalS $ do
      a <- number lim
      allSetSolutionsDo $ \s -> do
        let r = pick a s
        -- trace ("solution " ++ show r) (return ())
        when (r < 0 || r >= lim) (error "bad value")

  it "lessThanConstraint works" $ do
    let lim = 4
    evalS $ do
      a <- number lim
      b <- number lim
      lessThanConstraint a b
      lift (print (a, b))
      dumpClauses
      allSetSolutionsDo $ \s -> do
        let an = pick a s
        let bn = pick b s
        trace ("solution " ++ show (an, bn)) (return ())
        when (an < 0 || an >= lim) (error "bad value")
        when (bn < 0 || bn >= lim) (error "bad value")
        when (bn <= an)            (error "not less than!")

  it "can encode cardinality constraints" $ evalS $ do
    let card = 3
    a <- arena 7
    cardinality a card
    -- dumpClauses
    allSetSolutionsDo $ \s -> do
      let an    = pick a s
      let count = sum [ if x == 'x' then 1 else 0 | x <- an ]
      -- trace ("card " ++ show (an, count)) (return ())
      when (count /= card) (error "bad cardinality")

  it "can encode black blocks" $ do
    evalS $ do
      start <- number 5
      space <- arena 5
      blockConstraint start 3 space
      dumpClauses
      allSetSolutionsDo $ \s -> do
        let st = pick start s
        let sp = pick space s
        trace ("solution " ++ show (st, sp)) (return ())


main = do
  runS $ do
    let givens = n3
    ar  <- nonogram givens
    sol <- setSolution
    let fieldsStr      = pick ar sol
    let Givens w h _ _ = givens
    let fields = listArray
          ((1, 1), (w, h))
          [ if c == 'x' then Black else White | c <- fieldsStr ]
    let board = Board givens fields
    lift (print board)
  return ()

