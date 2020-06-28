module Main (main) where

import           Data.Array  (Array, listArray, (!), (//))
import           Data.List   (intercalate, transpose)
import qualified Data.Set    as S
import           Debug.Trace (trace)
import           Test.Hspec

import           Base

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
                     ns /= nums
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


main :: IO ()
main = do
  let e = empty n2
  mapM_ print (solutions e)

