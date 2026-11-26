import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-127,-1015/9), (-953/71,-119/9), (-419/93,-837/187), (-695/329,-347/165), (-137/119,-547/477), (-105/151,-419/605), (-161/351,-321/703), (-257/767,-1/3), (-55/201,-219/805)]
private def upperBoxes : Boxes := [(-995/29,-497/15), (-57/7,-911/113), (-395/117,-789/235), (-325/187,-649/375), (-257/255,-513/511), (-199/313,-397/627), (-311/713,-155/357), (-63/193,-251/773), (-219/805,-109/403)]

theorem checkedPair1At18 : RootTracking.OrderedPair 9 (row 18 2) (row 19 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
