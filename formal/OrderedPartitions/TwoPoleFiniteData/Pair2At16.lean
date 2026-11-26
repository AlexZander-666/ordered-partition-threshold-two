import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-507/5,-253/3), (-117/11,-467/45), (-199/57,-397/115), (-79/49,-315/197), (-119/137,-237/275), (-11/21,-175/337), (-135/377,-67/189), (-7/25,-111/401)]
private def upperBoxes : Boxes := [(-127,-507/5), (-477/35,-119/9), (-419/93,-209/47), (-87/41,-347/165), (-137/119,-273/239), (-105/151,-209/303), (-161/351,-5/11), (-129/383,-1/3), (-55/201,-109/403)]

theorem checkedPair2At16 : RootTracking.OrderedPair 8 (row 16 2) (row 18 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
