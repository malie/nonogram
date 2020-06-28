module Base where

import           Data.Array (Array, listArray, (!), (//))
import           Data.List  (intercalate, transpose)

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
empty givens@Givens { nonogramWidth = w, nonogramHeight = h } =
  Board givens (listArray ((1, 1), (w, h)) (repeat Unknown))

place givens@Givens { nonogramWidth = w, nonogramHeight = h } gs =
      Board givens (listArray ((1, 1), (w, h)) (repeat Unknown) // gs)

instance Show Board where
  show (Board (Givens w h rowNums colNums) fs) = unlines
    (  map ((leftPad ++) . unwords) (transpose top)
    ++ [ le
         ++ "|"
         ++ concat [ charForField (fs ! (col, row)) | col <- [1 .. w] ]
         ++ "|"
       | (row, le) <- zip [1 .. h] left
       ]
    )
   where
    charForField Black   = "B "
    charForField White   = ". "
    charForField Unknown = "_ "
    left :: [String]
    left = padToSameLength (map (unwords . map show) rowNums)
    leftPad :: String
    leftPad = replicate (1 + length (head left)) ' '
    ntop    = maximum (map length colNums)
    top     = map (align . map show) colNums
    align xs = replicate (ntop - length xs) " " ++ xs


padToSameLength :: [String] -> [String]
padToSameLength xs = map pad xs
 where
  len = maximum (map length xs)
  pad x = replicate (len - length x) ' ' ++ x


n1 = Givens 5 5 [[2], [1], [4], [3], [3]] [[2], [1], [3], [1, 3], [1, 2]]
n2 = Givens 10
            10
            [[1, 7], [2, 7], [2, 7], [2, 6], [1, 4], [4], [3], [2], [1], [1]]
            [[3], [5], [2], [3, 3], [8], [8], [6], [4], [4], [4]]
n3 = Givens
  15
  15
  [ [12]
  , [1, 3, 1]
  , [1, 4]
  , [4]
  , [3, 7]
  , [2, 3, 6]
  , [1, 8]
  , [9]
  , [10]
  , [3, 3]
  , [4, 3]
  , [4, 1]
  , [1, 3, 2]
  , [5, 2]
  , [2, 2, 3]
  ]
  [ [1]
  , [2, 5]
  , [2, 4, 1]
  , [1, 1, 8]
  , [3, 7]
  , [1, 4, 3]
  , [4, 4, 1]
  , [4, 4]
  , [5, 3]
  , [1, 9]
  , [1, 7]
  , [1, 8]
  , [2, 3, 1]
  , [1, 2, 3]
  , [1, 2, 3]
  ]

-- https://www.nonograms.org/nonograms/i/33908
n4 = Givens
  15
  15
  [ [1,1]
  , [2,4]
  , [1,1,1]
  , [5]
  , [2,4]
  , [1,1,2,1]
  , [2,1,4,1]
  , [1,1,4,1]
  , [1,2,6]
  , [1,1,2,2,1]
  , [1,1,2,1,1,1]
  , [2,1,1,1]
  , [2,1,1,2,2]
  , [2,3,1]
  , [3,3]
  ]
  [ [5]
  , [3,1,2]
  , [1,1,2,1,2]
  , [3,2,1,1]
  , [1,4,2,1,1]
  , [1,1,2,1]
  , [1,1,1,1]
  , [3,3]
  , [4,1]
  , [4,1]
  , [5,1]
  , [5,4]
  , [1,1,1,1]
  , [2,5,1]
  , [2,1,1]
  ]
