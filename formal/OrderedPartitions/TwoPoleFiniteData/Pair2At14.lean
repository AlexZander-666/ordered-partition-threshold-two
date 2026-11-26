import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-253/3,-63), (-57/7,-227/29), (-93/35,-185/71), (-139/117,-69/59), (-99/157,-49/79), (-9/23,-71/185), (-57/199,-7/25)]
private def upperBoxes : Boxes := [(-127,-253/3), (-117/11,-233/23), (-199/57,-99/29), (-79/49,-157/99), (-119/137,-59/69), (-11/21,-87/169), (-17/47,-67/189), (-7/25,-55/201)]

theorem checkedPair2At14 : RootTracking.OrderedPair 7 (row 14 2) (row 16 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
