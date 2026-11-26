import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-509/3,-1017/7), (-965/59,-241/15), (-869/155,-217/39), (-745/279,-93/35), (-611/413,-305/207), (-485/539,-121/135), (-95/161,-379/645), (-301/723,-75/181), (-31/97,-247/777), (-109/403,-217/807)]
private def upperBoxes : Boxes := [(-1019/5,-509/3), (-975/49,-487/25), (-447/65,-893/131), (-785/239,-49/15), (-83/45,-663/361), (-17/15,-543/481), (-437/587,-109/147), (-175/337,-349/675), (-285/739,-71/185), (-241/783,-15/49), (-217/807,-27/101)]

theorem checkedPair2At20 : RootTracking.OrderedPair 10 (row 20 2) (row 22 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
