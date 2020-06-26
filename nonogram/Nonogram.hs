-- -*- haskell-mode-stylish-haskell-path: "stylish-haskell" -*-

module Main (main) where

import           Data.Array  (Array, listArray, (!), (//))
import           Data.List   (intercalate, transpose)
import qualified Data.Set    as S
import           Debug.Trace (trace)
import           Test.Hspec

data Givens = Givens
    { nonogramWidth  :: Int
    , nonogramHeight :: Int
    , rowNumbers     :: [[Int]]
    , columnNumbers  :: [[Int]]
    }
    deriving (Show)

data Field = Unknown
    | White
    | Black
    deriving (Eq, Show)

data Board = Board
    { givens :: Givens
    , fields :: Array (Int, Int) Field
    }

empty :: Givens -> Board
empty givens@(Givens { nonogramWidth = w, nonogramHeight = h }) =
  Board givens (listArray ((1,1), (w,h)) (repeat Unknown))

place givens@(Givens { nonogramWidth = w, nonogramHeight = h }) gs =
  Board givens ((listArray ((1,1), (w,h)) (repeat Unknown)) // gs)

instance Show Board where
  show (Board (Givens w h rowNums colNums) fs) =
    unlines
      (map ((leftPad++) . unwords) (transpose top)
      ++
      [
      le ++ "|" ++
      concat [
          charForField (fs ! (col, row))
          | col <- [1..w] ] ++ "|"
      | (row, le) <- zip [1..h] left
      ])
   where
    charForField Black   = "B "
    charForField White   = ". "
    charForField Unknown = "_ "
    left :: [String]
    left = padToSameLength (map (intercalate " " . map show) rowNums)
    leftPad :: String
    leftPad = replicate (1 + length (head left)) ' '
    ntop = maximum (map length colNums)
    top = map (align . map show) colNums
    align xs = replicate (ntop - length xs) " " ++ xs


padToSameLength :: [String] -> [String]
padToSameLength xs = map pad xs
  where
    len = maximum (map length xs)
    pad x = replicate (len - length x) ' ' ++ x


solutions :: Board -> [Board]
solutions (Board g@(Givens w h rowNums colNums) fs0) = recur allFields fs0
  where
    -- recur (t:_) _ | trace ("guessing " ++ show t ++ "...\n") False = undefined
    recur (t:ts) fs
      | fs ! t == Unknown =
          let fsw = fs // [(t, White)]
              fsb = fs // [(t, Black)]
          in
            (if anyContradiction g fsw t then
               []
              else
               recur ts fsw)
            ++
            (if anyContradiction g fsb t then
               []
              else
                recur ts fsb)
      | fs ! t /= Unknown = recur ts fs
    recur [] fs = [Board g fs]
    allFields = [(col,row) | row <- [1..h], col <- [1..w]]

data Detection = Sure [Int]
    | Possibly [Int]
    deriving (Eq, Show)

anyContradictionBoard (Board g fs) t = anyContradiction g fs t

anyContradiction :: Givens -> Array (Int,Int) Field -> (Int,Int) -> Bool
anyContradiction (Givens w h rowNums colNums) fs (col,row) =
  ac rowFields (rowNums !! pred row)
  || ac colFields (colNums !! pred col)
  where
    colFields = [fs ! (col, r) | r <- [1..h]]
    rowFields = [fs ! (c, row) | c <- [1..w]]
    ac fs nums = case detect ([White] ++ fs ++ [White]) [] True of
      Sure ns     -> -- trace (show ("ac", ns, nums))
                     (ns /= nums)
      Possibly ns -> not (S.isSubsetOf (S.fromList ns) (S.fromList nums))


detect :: [Field] -> [Int] -> Bool -> Detection
detect [] res            True     = Sure (reverse res)
detect [] res            False    = Possibly (reverse res)
detect (White:Black:xs) res cer   = count xs 1 res cer
detect (White:xs) res      cer    = detect xs res cer
detect (Unknown:xs) res       cer = detect xs res False

count :: [Field] -> Int -> [Int] -> Bool -> Detection
count l@(White:xs) n res cer   = detect l (n:res) cer
count (Black:xs) n res   cer   = count xs (succ n) res cer
count (Unknown:xs) _ res     _ = detect xs res False

spec = describe "detec and count and anyContradiction" $ do
  it "works for wbw" (shouldBe (detect [White,Black,White] [] True) (Sure [1]))
  it "works for wwbbww"
    (shouldBe (detect [White,White,Black,Black,White,White] [] True) (Sure [2]))
  it "works for wbwbw"
    (shouldBe (detect [White,Black,White,Black,White] [] True) (Sure [1,1]))
  it "works for wbwx"
    (shouldBe (detect [White,Black,White,Unknown] [] True) (Possibly [1]))
  it "works for wbxw"
    (shouldBe (detect [White,Black,Unknown,White] [] True) (Possibly []))
  it "accepts ok"
    (shouldBe
     (anyContradictionBoard
       (place n1 [((1,1),White), ((2,1),White), ((3,1),White),
                  ((4,1),Black), ((5,1),Black)]) (5,1))
      False)


n1 = Givens 5 5 [[2],[1],[4],[3],[3]] [[2], [1], [3], [1,3], [1,2]]
n2 = Givens 10 10 [[1,7],[2,7],[2,7],[2,6],[1,4],[4],[3],[2],[1],[1]]
        [[3],[5],[2],[3,3],[8],[8],[6],[4],[4],[4]]
n3 = Givens 15 15
       [[12],[1,3,1],[1,4],[4],[3,7],
        [2,3,6],[1,8],[9],[10],[3,3],
        [4,3],[4,1],[1,3,2],[5,2],[2,2,3]]
       [[1],[2,5],[2,4,1],[1,1,8],[3,7],
        [1,4,3],[4,4,1],[4,4],[5,3],[1,9],
        [1,7],[1,8],[2,3,1],[1,2,3],[1,2,3]]

main :: IO ()
main = do
  let e = (empty n2)
  mapM_ print (solutions e)

