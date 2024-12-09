
namespace AoC2021D2

def content : String := include_str "../../data/AoC2021_day2.txt"


def process_data (s : String) : List Int :=
  s.replace "\x0d\n" " " |>.replace "\n" " "
  |>.splitOn " " |>.map String.toInt!

#eval content

inductive Command
| Forward
| Down
| Up


def parseCmd : String → Command
| "forward" => Command.Forward
| "down" => Command.Down
| "up" => Command.Up
| _ => Command.Forward
