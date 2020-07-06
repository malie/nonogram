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
newtype Number = Number [Var]  deriving (Eq, Show)
newtype Vec = Vec [Var] deriving (Eq, Show)
type Clause = [Int]

type SetSolution = S.Set Int

class Pick a where
  type P a
  pick :: a -> SetSolution -> P a

instance Pick Number where
  type P Number = Int
  pick (Number vars) sol =
    fromMaybe (error "bad") (findIndex (`S.member` sol) vars)

instance Pick Vec where
  type P Vec = String
  pick (Vec vars) sol = map l vars
    where l v = if S.member v sol then 'x' else 'o'


numberVars (Number xs) = xs

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

vec :: Int -> StateT S IO Vec
vec n = Vec <$> allocVars n

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

blockConstraint :: Number -> Int -> Vec -> StateT S IO ()
blockConstraint start@(Number startVars) len (Vec vec) = do
  let (sa, sb) = splitAt (length startVars - len + 1) startVars
  allFalse sb
  sequence_
    [ pr st 0 (take (len + 2) ar)
    | (st, ar) <- zip sa (tails ([falseVar] ++ vec ++ [falseVar]))
    ]
 where
  pr _ i _ | i == len + 2                   = return ()
  pr st i (r : rs) | i == 0 || i == len + 1 = do
    clause [-st, -r]
    pr st (succ i) rs
  pr st i (r : rs) = do
    clause [-st, r]
    pr st (succ i) rs


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
    -- allocate a "start position" for every given number
    startPositions <- replicateM (length givenNums) (number size)
    growingList startPositions
    -- minimalDistance givenNums startPositions
    -- minimalDistance (reverse givenNums)
    --                 (reverse (map reverseNumbers startPositions))

    shrinkRange givenNums startPositions
    shrinkRange (reverse givenNums) (reverse (map reverseNumbers startPositions))

    let fs = extract coord
    zipWithM_ (\start givenNum -> blockConstraint start givenNum (Vec fs))
              startPositions
              givenNums
    let s = sum givenNums
    cardinality (Vec fs) s

reverseNumbers (Number xs) = Number (reverse xs)

extractRow array row = [ array ! (c, row) | c <- [1 .. w] ]
  where (_, (w, _)) = bounds array

extractCol array col = [ array ! (col, r) | r <- [1 .. h] ]
  where (_, (_, h)) = bounds array

-- | every list element is smaller than the next one
growingList :: [Number] -> StateT S IO ()
growingList xs = zipWithM_ lessThanConstraint xs (tail xs)

-- | every list element is smaller than the next one.
-- Additionally the distance is at list dist
minimalDistance :: [Int] -> [Number] -> StateT S IO ()
minimalDistance dist xs = zip3WithM_ f xs (tail xs) dist
  where f x y d = do
          let yd = subtractConst y d
          clause (numberVars yd) -- at least one of them...
          -- exactlyOne (numberVars yd)
          lessThanConstraint x yd
          allFalse (allLessThan y d)

-- | shrink range of vars
shrinkRange :: [Int] -> [Number] -> StateT S IO ()
shrinkRange dist xs = f xs dist 0
  where
    f [] _ _ = return ()
    f (x:xs) (d:dist) sum = do
          allFalse (take sum (numberVars x))
          f xs dist (sum+d+1)

zip3WithM_ :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m ()
zip3WithM_ a (x:xs) (y:ys) (z:zs) = a x y z >> zip3WithM_ a xs ys zs
zip3WithM_ _ _ _ _                = return ()

cardinality (Vec xs) n = do
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

subtractConst :: Number -> Int -> Number
subtractConst (Number xs) n = Number (drop n xs)

allLessThan :: Number -> Int -> [Var]
allLessThan (Number xs) n = take n xs

foldTree :: (a -> a -> StateT S IO a) -> [a] -> StateT S IO a
foldTree _ [x] = return x
foldTree f xs  = pass xs >>= foldTree f
 where
  pass (a : b : rest) = do
    e  <- f a b
    ee <- pass rest
    return (e : ee)
  pass x = return x


data T a = T (T a) (T a)
    | L a
    deriving (Show)
test = foldTree (\a b -> return (T a b)) (map L [3, 4, 5, 6, 78])

spec = describe "solve sat" $ do
  it "can alloc vars" $ do
    let lim = 5
    r <- evalS $ do
      a <- number lim
      pick a <$> setSolution
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
    a <- vec 7
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
      space <- vec 5
      blockConstraint start 3 space
      dumpClauses
      allSetSolutionsDo $ \s -> do
        let st = pick start s
        let sp = pick space s
        trace ("solution " ++ show (st, sp)) (return ())

cnfStats = do
  cs <- gets clauses
  let histo = M.fromListWith (+) [ (length c, 1) | c <- cs ]
  return
    (  "num clauses: "
    ++ show (length cs)
    ++ "\nnum clauses by size:\n"
    ++ unlines (map (("   " ++) . show) (M.toList histo))
    )

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
    stats <- cnfStats
    lift (print ("encoding ms", fromIntegral (mid - start) / (10 ^ 9)))
    lift (print ("picosat ms", fromIntegral (finished - mid) / (10 ^ 9)))
    lift (putStrLn stats)
  return ()

