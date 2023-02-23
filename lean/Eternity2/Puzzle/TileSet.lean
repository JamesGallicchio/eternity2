import Eternity2.Puzzle.Board

namespace Eternity2

open Std

structure TileSet (size : Nat) (tile : Type u) where
  tiles : List (tile)
  h_ts : tiles.length = size * size

instance [BEq t] : BEq (TileSet s t) := ⟨(·.tiles == ·.tiles)⟩

namespace TileSet

instance [Inhabited tile] : Inhabited (TileSet size tile) where
  default := {
    tiles := List.replicate (size * size) default
    h_ts := by simp
  }

nonrec def toString [ToString tile] (ts : TileSet size tile) : String :=
  ts.tiles.map (toString ·)
  |>.map (·.splitOn "\n")
  |>.foldl (fun L1 L2 => List.zipWith (· ++ " " ++ ·) L1 L2) ["","",""]
  |> String.intercalate "\n"

instance [ToString tile] : ToString (TileSet size tile) := ⟨toString⟩
