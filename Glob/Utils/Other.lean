import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.Data.NonEmptyString
import Glob.Data.NonEmptyList
import Glob.Utils.NEFromTo

open System (FilePath)

private abbrev LNES := List NonEmptyString
private abbrev NELNES := NonEmptyList NonEmptyString

-- \f<< \-> \f>>
@[inline] def FilePath.Lax.«→LNES» (p : FilePath) : LNES := ToNE.FilterMap.«LS->LNES» p.components
@[inline] def FilePath.Lax.«→NELNES»  (p : FilePath) : Option NELNES := ToNE.FilterMap.«LS->NELNES» p.components
@[inline] def FilePath.Strict.«→LNES» (p : FilePath) : Option LNES := ToNE.Traverse.«LS->LNES» p.components
@[inline] def FilePath.Strict.«→NELNES» (p : FilePath) : Option NELNES := ToNE.Traverse.«LS->NELNES» p.components
