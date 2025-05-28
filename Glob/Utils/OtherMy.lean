import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.Utils.NonEmptyString
import Glob.Utils.NonEmptyList
import Glob.Utils.NEFromTo

open System (FilePath)


def FilePath.componentsNES (p : FilePath) : List NonEmptyString := ToNE.FilterMap.«LS->LNES» p.components
