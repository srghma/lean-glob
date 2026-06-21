module
public import Glob
public import TypedGlob
public import TypedPath.PosixPath
public import TypedPath.WindowsPath
public import Init.System.IO
public import Init.System.FilePath
public import LSpec
public meta import LSpec.LSpec

@[expose] public section

open System (FilePath)
open LSpec

def spec : TestSeq :=
  test "Posix toFilePath" ((IsTypedPath.parseValid (P:=Posix.ValidPath) "/foo/bar").map IsTypedPath.toFilePath == some (FilePath.mk "/foo/bar")) $
  test "Windows toFilePath" ((IsTypedPath.parseValid (P:=Windows.ValidPath) "C:\\foo\\bar").map IsTypedPath.toFilePath == some (FilePath.mk "C:\\foo\\bar"))

#lspec spec
end
