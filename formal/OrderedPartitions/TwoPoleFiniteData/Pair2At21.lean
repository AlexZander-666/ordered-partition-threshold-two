import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-125/3,-31), (-117/11,-29/3), (-13/3,-103/25), (-11/5,-87/41), (-9/7,-71/57), (-29/35,-57/71), (-23/41,-45/83), (-37/91,-9/23), (-31/97,-15/49), (-7/25,-27/101)]
private def upperBoxes : Boxes := [(-63,-125/3), (-119/9,-59/5), (-107/21,-53/11), (-47/17,-93/35), (-79/49,-39/25), (-65/63,-1), (-53/75,-13/19), (-43/85,-21/43), (-35/93,-17/47), (-15/49,-29/99), (-27/101,-13/51)]

theorem checkedPair2At21 : RootTracking.OrderedPair 10 (row 21 2) (row 23 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
