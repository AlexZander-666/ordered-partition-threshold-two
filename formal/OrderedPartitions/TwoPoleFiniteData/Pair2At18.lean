import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-127,-507/5), (-477/35,-119/9), (-419/93,-209/47), (-87/41,-347/165), (-137/119,-273/239), (-105/151,-209/303), (-161/351,-5/11), (-129/383,-1/3), (-55/201,-109/403)]
private def upperBoxes : Boxes := [(-509/3,-127), (-483/29,-241/15), (-435/77,-217/39), (-373/139,-93/35), (-153/103,-305/207), (-243/269,-121/135), (-95/161,-189/323), (-151/361,-75/181), (-31/97,-123/389), (-109/403,-27/101)]

theorem checkedPair2At18 : RootTracking.OrderedPair 9 (row 18 2) (row 20 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
