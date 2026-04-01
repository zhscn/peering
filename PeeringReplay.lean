import Peering

open Peering

def usage : String :=
  "usage: peering-replay <trace.jsonl>\n" ++
  "       peering-replay -\n"

def readInput (path : String) : IO String := do
  if path = "-" then
    let stdin ← IO.getStdin
    stdin.readToEnd
  else
    IO.FS.readFile path

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let input ← readInput path
      match replayTrace input with
      | .ok (stats, _) =>
          IO.println s!"replay ok: steps={stats.steps} summaries={stats.summaries}"
          pure 0
      | .error err =>
          IO.eprintln err
          pure 1
  | _ =>
      IO.eprintln usage
      pure 2
