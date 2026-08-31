namespace TSLean.Examples.Roundtrip.Window

/-- Whether each end of a range is open. -/
structure Window where
  lowerOpen : Bool
  upperOpen : Bool
  deriving DecidableEq, Repr

/-- Whether the window is open at both ends. -/
def Window.fullyOpen (window : Window) : Bool :=
  window.lowerOpen && window.upperOpen

/-- The window with both ends swapped. -/
def Window.flip (window : Window) : Window :=
  { lowerOpen := window.upperOpen, upperOpen := window.lowerOpen }

/-- Flipping twice returns the window it started from. -/
theorem flip_flip (window : Window) : window.flip.flip = window := by
  cases window
  rfl

end TSLean.Examples.Roundtrip.Window
