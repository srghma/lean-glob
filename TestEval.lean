import Lean.Data.Lsp.Utf16
def SEGMENT_MAX := 255
def foo : "x".utf16Length ≤ SEGMENT_MAX := by native_decide
