import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-249/7,-497/15), (-57/7,-455/57), (-395/117,-197/59), (-325/187,-81/47), (-257/255,-1), (-199/313,-99/157), (-39/89,-155/357), (-63/193,-125/387), (-55/201,-109/403)]
private def upperBoxes : Boxes := [(-509/3,-127), (-483/29,-241/15), (-435/77,-217/39), (-373/139,-93/35), (-153/103,-305/207), (-243/269,-121/135), (-95/161,-189/323), (-151/361,-75/181), (-31/97,-123/389), (-109/403,-27/101)]

theorem checkedPair1At19 : RootTracking.OrderedPair 9 (row 19 2) (row 20 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
