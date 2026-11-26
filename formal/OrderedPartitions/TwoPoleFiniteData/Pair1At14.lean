import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-253/3,-505/7), (-455/57,-227/29), (-371/141,-185/71), (-277/235,-69/59), (-99/157,-197/315), (-9/23,-143/369), (-57/199,-113/399)]
private def upperBoxes : Boxes := [(-489/23,-61/3), (-427/85,-213/43), (-171/85,-341/171), (-1,-255/257), (-93/163,-185/327), (-139/373,-69/187), (-113/399,-7/25)]

theorem checkedPair1At14 : RootTracking.OrderedPair 7 (row 14 2) (row 15 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
