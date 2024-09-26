{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections       #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
module Main where

import qualified Control.Monad.State.Strict as S
import qualified Data.Tree                  as T
import qualified Data.Vector.Unboxed        as V

import           Data.Maybe                 (fromJust, fromMaybe, isJust,
                                             isNothing)
import           Data.Word                  (Word8)
import           Flow                       ((.>), (|>))
import           Text.Printf                (printf)

--------------------------------------------------------------------------------

singIf :: Bool -> a -> [a]
singIf True  a = [a]
singIf False _ = [ ]

--------------------------------------------------------------------------------

data Player = PlayerA | PlayerB
  deriving (Eq)

instance Show Player where
  show PlayerA = "A"
  show PlayerB = "B"

otherPlayer :: Player -> Player
otherPlayer PlayerA = PlayerB
otherPlayer PlayerB = PlayerA

--------------------------------------------------------------------------------

type Side = V.Vector Word8

getInnerPos :: Int -> Int
getInnerPos = (23 -)

getOuterPos :: Int -> Int
getOuterPos = subtract 8

getSafe :: Int -> Side -> Word8
getSafe pos side = side V.!? pos |> fromMaybe 0

getInnerVal :: Int -> Side -> Word8
getInnerVal = getInnerPos .> getSafe

getOuterVal :: Int -> Side -> Word8
getOuterVal = getOuterPos .> getSafe

--------------------------------------------------------------------------------

data Board
  = Board
    { sideA :: !Side
    , sideB :: !Side
    }

initialBoard :: Board
initialBoard = let
  initialSide = V.generate 16 (\i -> if i `elem` [0..7] ++ [12..15] then 2 else 0)
  in Board initialSide initialSide

getBoardSide :: Player -> Board -> Side
getBoardSide PlayerA board = board.sideA
getBoardSide PlayerB board = board.sideB

setBoardSide :: Player -> Side -> Board -> Board
setBoardSide PlayerA side board = board { sideA = side }
setBoardSide PlayerB side board = board { sideB = side }

showBoardFor :: Player -> Board -> String
showBoardFor player board = let
  showRow :: Side -> String
  showRow = V.toList .> concatMap (printf "[%02d]")

  outerA = V.slice 0 8 board.sideA
  innerA = V.slice 8 8 board.sideA
  outerB = V.slice 0 8 board.sideB
  innerB = V.slice 8 8 board.sideB

  showAll a b c d =
    [ printf "%s| %s" (otherPlayer player |> show) (showRow a)
    , printf  " | %s" (V.reverse b |> showRow)
    , printf  "-+-%s" (replicate 32 '-')
    , printf  " | %s" (showRow c)
    , printf "%s| %s" (show player) (V.reverse d |> showRow) ]
    |> unlines

  in case player of
    PlayerA -> showAll outerB innerB innerA outerA
    PlayerB -> showAll outerA innerA innerB outerB

{-
B| [00][01][02][03][04][05][06][07]
 | [15][14][13][12][11][10][09][08]
-+---------------------------------
 | [08][09][10][11][12][13][14][15]
A| [07][06][05][04][03][02][01][00]
-}

--------------------------------------------------------------------------------

data Game
  = Game
    { board       :: !Board
    , player      :: !Player
    , previousPos :: !(Maybe Int)
    }

instance Show Game where
  show game =
    showBoardFor game.player game.board
    ++ maybe "No active cell" (printf "Active cell: %d") game.previousPos

initialGame :: Game
initialGame = Game initialBoard PlayerA Nothing

--------------------------------------------------------------------------------

data Takes = TakesNone | TakesOne | TakesBoth
  deriving (Enum, Eq, Ord, Show)

data Move
  = MoveFrom !Int
  | MoveCont !Takes
  | MoveStop
  deriving (Eq, Ord, Show)

legalMoves :: Game -> [Move]
legalMoves game = let
  mySide = getBoardSide              game.player  game.board
  enSide = getBoardSide (otherPlayer game.player) game.board
  in case game.previousPos of
    Nothing ->
      V.findIndices (>= 2) mySide |> V.toList |> map MoveFrom
    Just pos ->
      [ (MoveStop          , True)
      , (MoveCont TakesNone, mySide V.! pos > 1)
      , (MoveCont TakesOne , getInnerVal pos enSide > 0)
      , (MoveCont TakesBoth, getOuterVal pos enSide > 0) ]
      |> takeWhile snd |> map fst

sow :: Int -> Word8 -> Side -> (Int, Side)
sow pos extra side = let
  count = side V.! pos |> (+ extra) |> fromEnum
  indices = [pos + 1 .. pos + count] |> map (`mod` 16)
  in
  map ((side V.!) .> (+ 1)) indices
  |> zip indices
  |> ((pos, 0) :)
  |> (side V.//)
  |> ((pos + count) `mod` 16,)

doMove :: Move -> Game -> Game
doMove (MoveFrom pos) game | isNothing game.previousPos =
  getBoardSide game.player game.board
  |> sow pos 0
  |> \(endPos, side) -> game
  { board       = setBoardSide game.player side game.board
  , previousPos = Just endPos }

doMove (MoveCont takes) game | isJust game.previousPos = let
  mySide = getBoardSide              game.player  game.board
  enSide = getBoardSide (otherPlayer game.player) game.board

  startPos = fromJust game.previousPos
  innerPos = getInnerPos startPos
  outerPos = getOuterPos startPos
  innerVal = getInnerVal startPos enSide
  outerVal = getOuterVal startPos enSide

  (endPos, mySide') =
    [ singIf (takes >= TakesOne ) innerVal
    , singIf (takes == TakesBoth) outerVal ]
    |> concat |> sum |> \x -> sow startPos x mySide

  enSide' =
    [ singIf (takes >= TakesOne ) innerPos
    , singIf (takes == TakesBoth) outerPos ]
    |> concat |> map (, 0) |> (enSide V.//)
  in game
  { board =
    game.board
    |> setBoardSide              game.player  mySide'
    |> setBoardSide (otherPlayer game.player) enSide'
  , previousPos = Just endPos }

doMove MoveStop game | isJust game.previousPos =
  game { player = otherPlayer game.player, previousPos = Nothing }

doMove _ _ = error "Illegal move"

--------------------------------------------------------------------------------

type LegalMoves = Int
type Node = (Move, Game, LegalMoves)
type Tree = T.Tree Node

buildTree :: Node -> Tree
buildTree =
  T.unfoldTree (\node@(_, game, _) ->
  legalMoves game
  |> map (\m -> let g = doMove m game in (m, g, legalMoves g |> length))
  |> (node,))

pruneTree :: Int -> Tree -> Tree
pruneTree depth tree
  | depth <= 0 = tree { T.subForest = [] }
  | otherwise  = tree { T.subForest = map (pruneTree (depth - 1)) tree.subForest }

exampleTree :: Tree
exampleTree =
  (MoveStop, initialGame, legalMoves initialGame |> length)
  |> buildTree |> pruneTree 4

-- printTree = D.renderTree _

--------------------------------------------------------------------------------

type Run = S.StateT Game IO ()

printGame :: Game -> IO ()
printGame game = do
  print game
  print (legalMoves game)
  putStrLn ""

move :: Move -> Run
move m = do
  doMove m |> S.modify
  game <- S.get
  printGame game |> S.liftIO

example :: [Move]
example =
  [ MoveFrom 0
  , MoveCont TakesNone
  , MoveCont TakesNone
  , MoveStop
  , MoveFrom 13
  , MoveCont TakesBoth
  , MoveStop ]

main :: IO ()
main = do
  printGame initialGame
  mapM_ move example |> flip S.evalStateT initialGame
