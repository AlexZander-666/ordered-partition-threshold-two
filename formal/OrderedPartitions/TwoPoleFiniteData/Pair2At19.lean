import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-249/7,-497/15), (-57/7,-455/57), (-395/117,-197/59), (-325/187,-81/47), (-257/255,-1), (-199/313,-99/157), (-39/89,-155/357), (-63/193,-125/387), (-55/201,-109/403)]
private def upperBoxes : Boxes := [(-125/3,-499/13), (-233/23,-465/47), (-207/49,-413/99), (-11/5,-351/161), (-9/7,-287/225), (-115/141,-229/283), (-91/165,-181/331), (-73/183,-145/367), (-61/195,-121/391), (-109/403,-27/101)]

theorem checkedPair2At19 : RootTracking.OrderedPair 9 (row 19 2) (row 21 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
