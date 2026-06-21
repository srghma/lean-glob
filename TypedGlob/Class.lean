module
public import TypedPath.PosixPath
public import TypedPath.WindowsPath
public import Init.System.FilePath

@[expose] public section

class IsTypedPath (P : Type) where
  toFilePath : P → System.FilePath
  parseValid : String → Option P
  toString : P → String

instance : IsTypedPath Posix.ValidPath where
  toFilePath p := System.FilePath.mk (ToString.toString p)
  parseValid := Posix.parsePosixPath
  toString := ToString.toString

instance : IsTypedPath Windows.ValidPath where
  toFilePath p := System.FilePath.mk (ToString.toString p)
  parseValid := Windows.parseWindowsPath
  toString := ToString.toString

end
